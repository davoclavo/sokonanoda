// SPDX-FileCopyrightText: 2026 Jeremy Chen
// SPDX-License-Identifier: Apache-2.0

use crate::checker::cache::TcCache;
use crate::checker::context::{ExportFile, TcCtx};
use crate::checker::env::{Declar, DeclarInfo, Env, EnvLimit};
use crate::checker::value::E;
use crate::outcome::CheckError;
use crate::outcome::ensure;
use crate::report::Reporter;
use crate::term::ptr::ExprPtr;

/// The share of the cache that all of the checker threads together may hold.
/// One thread gets the whole share. Each extra thread divides it.
const CACHE_SHARE: usize = 16 * 1024 * 1024;

/// The smallest session budget. Below this value a session resets so often that
/// it drops cache entries it is about to need again.
const SESSION_FLOOR: usize = 2 * 1024 * 1024;

/// How many bytes a checking session may allocate before it resets its arena
/// and drops its per-session caches. The budget trades cache hits against cache
/// locality, and the threads compete for one cache, so the budget is a share.
/// Measured on the arena corpora: at one thread 16 MiB beats 2 MiB by 8 percent
/// on std and 2 percent on cedar, and at four threads 2 MiB beats 16 MiB by 5
/// percent on cedar.
fn session_budget(num_threads: usize) -> usize {
    // TEMPORARY sweep hook. Remove before the commit.
    if let Ok(mib) = std::env::var("SOKO_SESSION_BUDGET")
        && let Ok(mib) = mib.parse::<usize>()
    {
        return mib * 1024 * 1024;
    }
    (CACHE_SHARE / num_threads.max(1)).max(SESSION_FLOOR)
}

const CHUNK_SIZE: usize = 64;

/// An enum for type safety and convenience; used during nat literal reduction, and also for testing.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum NatBinOp {
    Add,
    Sub,
    Mul,
    Pow,
    Mod,
    Div,
    Beq,
    Ble,
    Gcd,
    LAnd,
    LOr,
    XOr,
    Shl,
    Shr,
}

/// A flag that accompanies calls to type inference; if the flag is `Check`,
/// we perform additional definitional equality checks (for example, the type of an
/// argument to a lambda is the same type as the binder in the labmda). These checks
/// are costly however, and in some cases we're using inference during reduction of
/// expressions we know to be well-typed, so we can pass the flag `InferOnly` to omit
/// these checks when they are not needed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum InferFlag {
    InferOnly,
    Check,
}

pub struct TypeChecker<'x, 't, 'p> {
    pub(crate) ctx: &'x mut TcCtx<'t, 'p>,
    /// An immutable reference to an environment, which contains declarations and notation.
    /// To accommodate the temporary declarations created while checking nested inductives,
    /// the environment may have a temporary extension which also holds declarations, and
    /// is searched before the persistent environment.
    ///
    /// This is stored as a field in `TypeChecker` rather than being placed in `TcCtx` so
    /// that the borrow checker will allow us to mutably reference `TcCtx` while we have
    /// outstanding references to environment declarations. Rust can tell that borrows
    /// of different struct fields are exclusive, but it can't analyze what fields of a given
    /// field's type are being exclusively borrowed.
    pub(crate) env: &'x Env<'x, 't>,
    /// The caches for things like inference, reduction, and equality checking.
    pub(crate) tc_cache: &'x mut TcCache<'t, 't>,
    pub(crate) arena: &'t bumpalo::Bump,
    /// If this type checker is being used to check a simple declaration, this field will
    /// contain the universe parameters of that declaration. This is used in a couple of places
    /// to make sure that all of the universe paramters actually used in a declaration `d` are
    /// properly represented in the declaration's uparams info.
    pub(crate) declar_info: Option<DeclarInfo<'t>>,
    pub(crate) nat_extension: bool,
    pub(crate) ordered_declaration: bool,
    /// `true` while this type checker checks an `unsafe` or a `partial` declaration.
    /// Such a declaration can refer to another `unsafe` or `partial` declaration.
    /// A safe declaration cannot. This mirrors `definition_safety` in the Lean kernel.
    pub(crate) allow_unsafe: bool,
}

impl<'p> ExportFile<'p> {
    fn check_declar_with<'t>(
        &'t self,
        ctx: &mut TcCtx<'t, 'p>,
        cache: &mut TcCache<'t, 't>,
        bump: &'t bumpalo::Bump,
        d: &Declar<'t>,
    ) {
        use Declar::{Inductive, Quot};
        match d {
            Inductive(..) => self.check_inductive_declar(ctx, cache, bump, d),
            Quot { .. } => crate::checker::quot::check_quot(ctx, cache, bump, d),
            _ => self.check_simple_declar(ctx, cache, bump, d),
        }
    }

    fn check_simple_declar<'t>(
        &'t self,
        ctx: &mut TcCtx<'t, 'p>,
        cache: &mut TcCache<'t, 't>,
        bump: &'t bumpalo::Bump,
        d: &Declar<'t>,
    ) {
        use Declar::{
            Axiom, Constructor, Definition, Inductive, Opaque, Quot, Recursor, Theorem, Unsafe,
        };
        let env = self.new_env(EnvLimit::ByName(d.info().name));
        let mut tc = TypeChecker::new(ctx, &env, bump, Some(*d.info()), cache);
        tc.ordered_declaration = true;
        tc.allow_unsafe = matches!(d, Unsafe { .. });
        match d {
            Definition { val, .. } | Theorem { val, .. } | Opaque { val, .. } => {
                tc.check_def_like_v(d, *val);
            }
            Axiom { .. } | Constructor(..) | Recursor(..) | Unsafe { .. } => {
                tc.check_declar_info_v(d);
            }
            Inductive(..) | Quot { .. } => unreachable!(),
        }
        match d {
            Constructor(ctor_data) => {
                ensure!(self.declars.get(&ctor_data.inductive_name).is_some());
            }
            Recursor(recursor_data) => {
                let rec_idx = self
                    .declars
                    .get_index_of(&recursor_data.info.name)
                    .expect("missing recursor");
                let first = *recursor_data
                    .all_inductives
                    .first()
                    .expect("recursor is not associated with an inductive block");
                let block = *self
                    .mutual_block_sizes
                    .get(&first)
                    .expect("recursor is associated with a non-inductive declaration");
                ensure!(
                    rec_idx >= block.0 && rec_idx < block.0 + block.1,
                    "recursor is not in its associated inductive block"
                );
                for ind_name in recursor_data.all_inductives.iter() {
                    ensure!(
                        matches!(self.declars.get(ind_name), Some(Inductive(..)))
                            && self.mutual_block_sizes.get(ind_name) == Some(&block),
                        "recursor is associated with a declaration outside its inductive block"
                    );
                }
            }
            _ => {}
        }
    }

    fn run_session<F>(&self, report: &Reporter, first: (usize, usize), mut next_chunk: F)
    where
        F: FnMut() -> Option<(usize, usize)>,
    {
        let thread_arena = bumpalo::Bump::new();
        let mut tctx = TcCtx::new(self, &thread_arena);
        self.run_session_inner(report, first, &mut next_chunk, &mut tctx);
    }

    fn run_session_inner<'h, F>(
        &'h self,
        report: &Reporter,
        first: (usize, usize),
        next_chunk: &mut F,
        tctx: &mut TcCtx<'h, 'p>,
    ) where
        F: FnMut() -> Option<(usize, usize)>,
    {
        let budget = session_budget(self.config.num_threads);
        let arena_keep = 4 * budget;
        let base = bumpalo::Bump::new();
        let mut session_cache = crate::checker::cache::SessionCache::new(&base);
        let mut sbump = crate::checker::cache::SessionBump::new();
        let ind_base = bumpalo::Bump::new();
        let mut ind_cache = crate::checker::cache::SessionCache::new_small(&ind_base);
        let mut ind_bump = crate::checker::cache::SessionBump::new();
        let mut pending = Some(first);
        loop {
            let finished = unsafe {
                session_cache.enter(|cache| {
                    loop {
                        let Some((mut i, end)) = pending.take().or_else(&mut *next_chunk) else {
                            return true;
                        };
                        while i < end {
                            let (_, d) = self
                                .declars
                                .get_index(i)
                                .expect("declaration index out of range");
                            i += 1;
                            if matches!(d, Declar::Inductive(..)) {
                                report.check(d, || {
                                    ind_cache.enter(|ind| {
                                        self.check_inductive_declar(tctx, ind, ind_bump.get(), d);
                                        true
                                    });
                                });
                                ind_bump.reset(arena_keep);
                                continue;
                            }
                            report.check(d, || self.check_declar_with(tctx, cache, sbump.get(), d));
                            if sbump.used_bytes() > budget {
                                pending = Some((i, end));
                                return false;
                            }
                        }
                    }
                })
            };
            sbump.reset(arena_keep);
            tctx.expr_cache.clear_session();
            if finished {
                return;
            }
        }
    }

    /// Check all declarations in this export file using a single thread.
    pub(crate) fn check_all_declars_serial(&self, report: &Reporter) {
        let total = self.declars.len();
        std::thread::scope(|sco| {
            std::thread::Builder::new()
                .stack_size(crate::STACK_SIZE)
                .spawn_scoped(sco, || self.run_session(report, (0, total), || None))
                .unwrap()
                .join()
                .unwrap_or_else(|payload| std::panic::resume_unwind(payload));
        });
    }

    /// Check all declarations in this export file, spawning `num_threads` as
    fn check_all_declars_par(&self, report: &Reporter, num_threads: usize) {
        use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};
        use std::thread;
        let task_num = AtomicUsize::new(0);
        let total = self.declars.len();
        let claim = || {
            let start = task_num.fetch_add(CHUNK_SIZE, Relaxed);
            if start >= total || report.stopped() {
                None
            } else {
                Some((start, (start + CHUNK_SIZE).min(total)))
            }
        };
        thread::scope(|sco| {
            let mut handles = Vec::new();
            for i in 0..num_threads {
                handles.push(
                    thread::Builder::new()
                        .name(format!("thread_{i}"))
                        .stack_size(crate::STACK_SIZE)
                        .spawn_scoped(sco, || {
                            if let Some(first) = claim() {
                                self.run_session(report, first, claim);
                            }
                        })
                        .unwrap(),
                );
            }
            for t in handles {
                t.join()
                    .unwrap_or_else(|payload| std::panic::resume_unwind(payload));
            }
        });
    }

    /// Check all of the declarations in this export file on the specified number
    /// of threads (checking will be serial on the main thread is `num_threads <= 1`).
    pub fn check_all_declars(&self) -> Result<(), CheckError> {
        let report = Reporter::new(&self.config, self.declars.len());
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            if self.config.parse_only {
                for (_, d) in &self.declars {
                    report.check(d, || {});
                }
            } else if self.config.num_threads > 1 {
                self.check_all_declars_par(&report, self.config.num_threads);
            } else {
                self.check_all_declars_serial(&report);
            }
        }));
        report.finish();
        result.map_err(CheckError::from_panic)
    }
}

impl<'x, 't: 'x, 'p: 't> TypeChecker<'x, 't, 'p> {
    pub fn new(
        dag: &'x mut TcCtx<'t, 'p>,
        env: &'x Env<'x, 't>,
        arena: &'t bumpalo::Bump,
        declar_info: Option<DeclarInfo<'t>>,
        tc_cache: &'x mut TcCache<'t, 't>,
    ) -> Self {
        let nat_extension = dag.export_file.config.nat_extension;
        dag.next_declaration();
        Self {
            ctx: dag,
            env,
            tc_cache,
            arena,
            declar_info,
            nat_extension,
            ordered_declaration: false,
            allow_unsafe: false,
        }
    }

    #[inline]
    pub(crate) fn empty_env(&self) -> E<'t> {
        self.tc_cache.empty_env
    }

    #[inline]
    pub(crate) fn empty_spine(&self) -> crate::checker::value::S<'t> {
        self.tc_cache.empty_spine
    }

    #[inline]
    pub(crate) fn empty_ctx(&self) -> crate::checker::value::C<'t> {
        self.tc_cache.empty_ctx
    }

    pub fn assert_def_eq(&mut self, u: ExprPtr<'t>, v: ExprPtr<'t>) {
        ensure!(self.def_eq_core(u, v), "def_eq failed");
    }
}

#[cfg(test)]
mod tests {
    use crate::config::Config;
    use crate::frontend::parser::parse_export_file;
    use crate::outcome::CheckError;
    use bumpalo::Bump;
    use std::error::Error;

    /// `False : Prop` with its recursor, followed by a definition of the given
    /// safety whose value is itself, and a theorem `bad : False` whose value is
    /// that definition.
    fn export_with(safety: &str, name: &str) -> String {
        format!(
            r#"{{"in":1,"str":{{"pre":0,"str":"False"}}}}
{{"ie":0,"sort":0}}
{{"in":2,"str":{{"pre":1,"str":"rec"}}}}
{{"in":3,"str":{{"pre":0,"str":"u"}}}}
{{"il":1,"param":3}}
{{"in":4,"str":{{"pre":0,"str":"motive"}}}}
{{"in":5,"str":{{"pre":0,"str":"t"}}}}
{{"const":{{"name":1,"us":[]}},"ie":1}}
{{"ie":2,"sort":1}}
{{"forallE":{{"binderInfo":"default","body":2,"name":5,"type":1}},"ie":3}}
{{"bvar":1,"ie":4}}
{{"bvar":0,"ie":5}}
{{"app":{{"arg":5,"fn":4}},"ie":6}}
{{"forallE":{{"binderInfo":"default","body":6,"name":5,"type":1}},"ie":7}}
{{"forallE":{{"binderInfo":"default","body":7,"name":4,"type":3}},"ie":8}}
{{"inductive":{{"ctors":[],"recs":[{{"all":[1],"isUnsafe":false,"k":false,"levelParams":[3],"name":2,"numIndices":0,"numMinors":0,"numMotives":1,"numParams":0,"rules":[],"type":8}}],"types":[{{"all":[1],"ctors":[],"isRec":false,"isReflexive":false,"isUnsafe":false,"levelParams":[],"name":1,"numIndices":0,"numNested":0,"numParams":0,"type":0}}]}}}}
{{"in":6,"str":{{"pre":0,"str":"{name}"}}}}
{{"const":{{"name":6,"us":[]}},"ie":9}}
{{"def":{{"all":[6],"hints":"opaque","levelParams":[],"name":6,"safety":"{safety}","type":1,"value":9}}}}
{{"in":7,"str":{{"pre":0,"str":"bad"}}}}
{{"thm":{{"all":[7],"levelParams":[],"name":7,"type":1,"value":9}}}}
"#
        )
    }

    fn check(export: &str) -> Result<Result<(), CheckError>, Box<dyn Error>> {
        let arena = Bump::new();
        let input = std::io::Cursor::new(export.as_bytes().to_vec());
        let export_file = parse_export_file(&arena, input, Config::default())?;
        Ok(export_file.check_all_declars())
    }

    fn rejection(export: &str) -> String {
        match check(export).expect("the export must parse") {
            Err(CheckError::Rejected(r)) => r.to_string(),
            other => panic!("expected a rejection, got {other:?}"),
        }
    }

    /// A safe declaration must not refer to an `unsafe` declaration. Declining the
    /// export instead would let a proof of `False` pass unexamined.
    #[test]
    fn reject_safe_declar_that_uses_unsafe() {
        let message = rejection(&export_with("unsafe", "unsafeLoop"));
        assert!(
            message.contains("it uses unsafe declaration 'unsafeLoop'"),
            "unexpected message: {message}"
        );
    }

    /// A safe declaration must not refer to a `partial` declaration.
    #[test]
    fn reject_safe_declar_that_uses_partial() {
        let message = rejection(&export_with("partial", "partialLoop"));
        assert!(
            message.contains("must not contain partial declaration 'partialLoop'"),
            "unexpected message: {message}"
        );
    }

    /// An `unsafe` declaration on its own is accepted. Its value is never checked,
    /// so a value that refers to itself does not loop.
    #[test]
    fn accept_unsafe_declar_that_nothing_safe_uses() {
        let export = export_with("unsafe", "unsafeLoop");
        let without_theorem = export
            .lines()
            .filter(|line| !line.contains("\"thm\""))
            .collect::<Vec<_>>()
            .join("\n");
        assert!(
            check(&without_theorem)
                .expect("the export must parse")
                .is_ok()
        );
    }
}
