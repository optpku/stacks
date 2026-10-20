module

public import Mathlib.FieldTheory.AlgebraicClosure
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open IntermediateField

variable (k K : Type*) [Field k] [Field K] [Algebra k K]

/- Domain-style sampling for Definition 9.26.9:
- primary domain: the algebraic closure of a base field `k` inside a field extension `K/k`, i.e. the
  subfield of `K` consisting of the elements of `K` that are algebraic over `k`;
- sampled owner declarations:
  `algebraicClosure`,
  `mem_algebraicClosure_iff`,
  `algebraicClosure_toSubalgebra`;
- best owner abstraction: the canonical owner is the mathlib intermediate field
  `algebraicClosure k K`, whose members are exactly the elements of `K` algebraic over `k`;
- primitive data: none locally beyond the ambient field extension `K/k`;
- derived API: `mem_algebraicClosure_iff` characterizes membership, and the property that `k` is
  algebraically closed in `K` is the vanishing `algebraicClosure k K = ⊥`.

Source/core/bridge triage:
- `source-facing`: the algebraic closure of `k` in `K`, and the notion of `k` being algebraically
  closed in `K`;
- `core/canonical`: `algebraicClosure`;
- `bridge/view`: `mem_algebraicClosure_iff` and the reformulation `algebraicClosure k K = ⊥`.

This item adds no new mathematics beyond the canonical owner, so the file remains a pure check
surface rather than introducing a redundant local wrapper. -/

/- Definition 9.26.9: the algebraic closure of `k` in a field extension `K/k` is the subfield `k'`
of `K` consisting of the elements of `K` that are algebraic over `k`; this is the canonical mathlib
intermediate field `algebraicClosure k K`. We say `k` is algebraically closed in `K` when every
element of `K` algebraic over `k` already lies in `k`, i.e. `algebraicClosure k K = ⊥`. -/
@[stacks 037I]
#check algebraicClosure

/- Membership bridge: an element of `K` lies in the algebraic closure of `k` in `K` exactly when it
is algebraic over `k`. -/
#check mem_algebraicClosure_iff

/- Bridge check: `k` is algebraically closed in `K` precisely when the algebraic closure of `k` in
`K` is the bottom subfield `k`. -/
#check (algebraicClosure k K = ⊥)
