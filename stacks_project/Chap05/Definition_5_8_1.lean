module

public import Mathlib.Topology.Irreducible
import StacksCheckRecall

@[expose] public section

/-
The space clause is owned by `IrreducibleSpace`; `irreducibleSpace_def` and
`isPreirreducible_iff_isClosed_union_isClosed` recover its set-level and closed-cover
presentations. The component clause is definitionally owned by `irreducibleComponents`, while
`irreducibleComponents_eq_maximals_closed` is a derived closed-set view. Recalling the two owners
keeps the source boundary at an arbitrary topological space and exposes the standard class and set
APIs downstream without parallel predicates.
-/

/- Definition 5.8.1 (1): a nonempty topological space is irreducible when a cover by two closed
subsets is already covered by one of them; the canonical owner is `IrreducibleSpace`. -/
@[stacks 004V "irreducible topological spaces"]
#check @IrreducibleSpace

/- Definition 5.8.1 (2): the irreducible components of a topological space are its maximal
irreducible subsets; the canonical owner is `irreducibleComponents`. -/
@[stacks 004V "irreducible components as maximal irreducible subsets"]
#check @irreducibleComponents
