module

public import Mathlib.Topology.Irreducible
import StacksCheckRecall

@[expose] public section

/-
The source needs four consequences for an arbitrary topological space. The verified canonical
owners are `IsIrreducible.closure` for the one-way closure claim, `irreducibleComponents` for
maximal irreducible subsets, and `irreducibleComponent` for a chosen component through a point;
`isIrreducible_iff_closure` is a useful stronger view, but not the source-facing direction.
Using the owner-level theorems below keeps exactly the boundary `[TopologicalSpace X]`.
`sUnion_irreducibleComponents` is the canonical set-level owner of the source's fourth clause; the
two point lemmas remain fine-grained companions that expose its canonical witness.
-/

universe u

variable {X : Type u} [TopologicalSpace X]

/- Lemma 5.8.3 (1): the closure of an irreducible subset of `X` is irreducible. -/
@[stacks 004W "closure of irreducible subsets"]
#check @IsIrreducible.closure

/- Lemma 5.8.3 (2): every irreducible component of `X` is closed. -/
@[stacks 004W "closedness of irreducible components"]
#check @isClosed_of_mem_irreducibleComponents

/- Lemma 5.8.3 (3): every irreducible subset of `X` is contained in an irreducible component of
`X`. -/
@[stacks 004W "irreducible subsets lie in irreducible components"]
#check @exists_mem_irreducibleComponents_subset_of_isIrreducible

/- Companion check: every point `x` of `X` lies in the canonical set
`irreducibleComponent x`. -/
#check @mem_irreducibleComponent

/- Companion check: `irreducibleComponent x` is an irreducible component of `X`. -/
#check @irreducibleComponent_mem_irreducibleComponents

/-
Lemma 5.8.3 (4): `X` is the union of its irreducible components, equivalently every point of `X`
lies in some irreducible component.
-/
@[stacks 004W "the space is the union of its irreducible components"]
#check @sUnion_irreducibleComponents
