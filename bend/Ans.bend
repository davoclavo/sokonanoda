# A three-valued answer: yes, no, or do not know.
#
# A kernel has three honest replies, not two. It can show a declaration is
# well typed, it can show it is not, and it can run out of the budget it was
# given and know neither. Reporting the third as a rejection is reporting
# falsely, and the arena has an exit code for it.
#
# `AUnk` spreads the way ignorance should: a conjunction is unknown unless
# some part is already a definite no, and a disjunction is unknown unless some
# part is already a definite yes.

import Base

type Ans is Data:
  AYes{}
  ANo{}
  AUnk{}

def Ans.of(b: Bool) -> Ans:
  match b:
    case True{}:
      AYes{}
    case False{}:
      ANo{}

# Not knowing, unless the other side is a definite no.
def Ans.unk_unless_no(b: Ans) -> Ans:
  match b:
    case ANo{}:
      ANo{}
    case o:
      AUnk{}

# Not knowing, unless the other side is a definite yes.
def Ans.unk_unless_yes(b: Ans) -> Ans:
  match b:
    case AYes{}:
      AYes{}
    case o:
      AUnk{}

# Both must hold. A definite no wins over not knowing, because a declaration
# that fails one check is wrong whatever the others would have said.
def Ans.and(a: Ans, b: Ans) -> Ans:
  match a:
    case ANo{}:
      ANo{}
    case AYes{}:
      b
    case AUnk{}:
      Ans.unk_unless_no(b)

# Either may hold. A definite yes wins over not knowing.
def Ans.or(a: Ans, b: Ans) -> Ans:
  match a:
    case AYes{}:
      AYes{}
    case ANo{}:
      b
    case AUnk{}:
      Ans.unk_unless_yes(b)

def Ans.is_yes(a: Ans) -> Bool:
  match a:
    case AYes{}:
      True{}
    case o:
      False{}

def Ans.is_no(a: Ans) -> Bool:
  match a:
    case ANo{}:
      True{}
    case o:
      False{}

def Ans.is_unk(a: Ans) -> Bool:
  match a:
    case AUnk{}:
      True{}
    case o:
      False{}

# `accept`, `reject`, or `declined`, which are the arena's three outcomes.
def Ans.show(a: Ans) -> String:
  match a:
    case AYes{}:
      "accept"
    case ANo{}:
      "reject"
    case AUnk{}:
      "declined"
