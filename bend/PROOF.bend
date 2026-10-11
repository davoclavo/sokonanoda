# The proofs. Each is an induction over the structure, with the induction
# hypothesis rewritten into the goal by `%`.
#
# The motive after `%` is the goal with `_` where the equation's right side
# sits. Every position left of the one being rewritten is already substituted;
# every position to its right still holds the original field.

import Base
import ./Level.bend as L
import ./Term.bend as T
import ./LAWS.bend as Laws

def Laws.level_subst_nil(l):
  match l:
    case L.LZero{}:
      {==}
    case L.LSucc{x}:
      %Laws.level_subst_nil(x) : {L.LSucc{L.Level.subst(x, [])} == L.LSucc{_} : L.Level}
      {==}
    case L.LMax{a, b}:
      %Laws.level_subst_nil(a) : {L.LMax{L.Level.subst(a, []), L.Level.subst(b, [])} == L.LMax{_, b} : L.Level}
      %Laws.level_subst_nil(b) : {L.LMax{L.Level.subst(a, []), L.Level.subst(b, [])} == L.LMax{L.Level.subst(a, []), _} : L.Level}
      {==}
    case L.LIMax{a, b}:
      %Laws.level_subst_nil(a) : {L.LIMax{L.Level.subst(a, []), L.Level.subst(b, [])} == L.LIMax{_, b} : L.Level}
      %Laws.level_subst_nil(b) : {L.LIMax{L.Level.subst(a, []), L.Level.subst(b, [])} == L.LIMax{L.Level.subst(a, []), _} : L.Level}
      {==}
    case L.LPar{i}:
      {==}

def Laws.level_list_nil(ls):
  match ls:
    case Nil{}:
      {==}
    case Con{h, t}:
      %Laws.level_subst_nil(h) : {Con{L.Level.subst(h, []), T.Term.subst_level_list(t, [])} == Con{_, t} : List<&2, L.Level>}
      %Laws.level_list_nil(t) : {Con{L.Level.subst(h, []), T.Term.subst_level_list(t, [])} == Con{L.Level.subst(h, []), _} : List<&2, L.Level>}
      {==}

def Laws.term_subst_levels_nil(t):
  match t:
    case T.TVar{i}:
      {==}
    case T.TSort{l}:
      %Laws.level_subst_nil(l) : {T.TSort{L.Level.subst(l, [])} == T.TSort{_} : T.Term}
      {==}
    case T.TConst{n, ls}:
      %Laws.level_list_nil(ls) : {T.TConst{n, T.Term.subst_level_list(ls, [])} == T.TConst{n, _} : T.Term}
      {==}
    case T.TApp{f, a}:
      %Laws.term_subst_levels_nil(f) : {T.TApp{T.Term.subst_levels(f, []), T.Term.subst_levels(a, [])} == T.TApp{_, a} : T.Term}
      %Laws.term_subst_levels_nil(a) : {T.TApp{T.Term.subst_levels(f, []), T.Term.subst_levels(a, [])} == T.TApp{T.Term.subst_levels(f, []), _} : T.Term}
      {==}
    case T.TLam{ty, bd}:
      %Laws.term_subst_levels_nil(ty) : {T.TLam{T.Term.subst_levels(ty, []), T.Term.subst_levels(bd, [])} == T.TLam{_, bd} : T.Term}
      %Laws.term_subst_levels_nil(bd) : {T.TLam{T.Term.subst_levels(ty, []), T.Term.subst_levels(bd, [])} == T.TLam{T.Term.subst_levels(ty, []), _} : T.Term}
      {==}
    case T.TPi{ty, bd}:
      %Laws.term_subst_levels_nil(ty) : {T.TPi{T.Term.subst_levels(ty, []), T.Term.subst_levels(bd, [])} == T.TPi{_, bd} : T.Term}
      %Laws.term_subst_levels_nil(bd) : {T.TPi{T.Term.subst_levels(ty, []), T.Term.subst_levels(bd, [])} == T.TPi{T.Term.subst_levels(ty, []), _} : T.Term}
      {==}
    case T.TProj{tn, idx, st}:
      %Laws.term_subst_levels_nil(st) : {T.TProj{tn, idx, T.Term.subst_levels(st, [])} == T.TProj{tn, idx, _} : T.Term}
      {==}
    case T.TUnk{}:
      {==}
    case T.TLet{ty, v, bd}:
      %Laws.term_subst_levels_nil(ty) : {T.TLet{T.Term.subst_levels(ty, []), T.Term.subst_levels(v, []), T.Term.subst_levels(bd, [])} == T.TLet{_, v, bd} : T.Term}
      %Laws.term_subst_levels_nil(v) : {T.TLet{T.Term.subst_levels(ty, []), T.Term.subst_levels(v, []), T.Term.subst_levels(bd, [])} == T.TLet{T.Term.subst_levels(ty, []), _, bd} : T.Term}
      %Laws.term_subst_levels_nil(bd) : {T.TLet{T.Term.subst_levels(ty, []), T.Term.subst_levels(v, []), T.Term.subst_levels(bd, [])} == T.TLet{T.Term.subst_levels(ty, []), T.Term.subst_levels(v, []), _} : T.Term}
      {==}
