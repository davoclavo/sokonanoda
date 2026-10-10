# The laws this kernel must obey. A human states them here and does not touch
# PROOF.bend; the proofs live there. `bend PROOF.bend` prints ALL PROOFS CHECK
# only when every law below is proven.
#
# These are structural facts the kernel leans on. Substituting an empty level
# assignment must change nothing: if it did, a declaration with no level
# parameters could be read at the wrong type.

import Base
import ./Level.bend as L
import ./Term.bend as T

# LAW: an empty level assignment leaves a level alone.
law level_subst_nil:
  for l: L.Level
  {L.Level.subst(l, []) == l : L.Level}

# LAW: an empty level assignment leaves a list of levels alone.
law level_list_nil:
  for ls: List<&2, L.Level>
  {T.Term.subst_level_list(ls, []) == ls : List<&2, L.Level>}

# LAW: an empty level assignment leaves a term alone.
law term_subst_levels_nil:
  for t: T.Term
  {T.Term.subst_levels(t, []) == t : T.Term}
