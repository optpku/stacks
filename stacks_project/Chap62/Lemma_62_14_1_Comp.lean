module

public import stacks_project.Chap62.Lemma_62_13_1_Comp
public import stacks_project.Chap62.Lemma_62_5_1_Operations
public import stacks_project.Chap62.Lemma_62_6_6_Family

/-!
# Composition of relative fibre-cycle families

This file wraps `CyclesOnFibers.comp` as an operation on `ℕ`-graded
`RelativeCycle.Family`, reindexing the composite degree along
`Int.natCast_add`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- Composition of a family of `r`-cycles on fibres of `X ⟶ Y` with a family of
`e`-cycles on fibres of `Y ⟶ S`, as a family of `(r + e)`-cycles on fibres of
`X ⟶ S`. -/
noncomputable def comp {S X Y : Scheme.{u}} {f : X ⟶ Y} {p : Y ⟶ S}
    [LocallyOfFiniteType f] [LocallyOfFiniteType p] {r e : ℕ}
    (α : Family f r) (β : Family p e) : Family (f ≫ p) (r + e) :=
  FiberCycleFamily.reindex (Int.natCast_add r e).symm (CyclesOnFibers.comp α β)

/-- Unfolding `comp` recovers reindexing of `CyclesOnFibers.comp` from degree
`(r : ℤ) + e` to `(r + e : ℤ)`. -/
theorem comp_def {S X Y : Scheme.{u}} {f : X ⟶ Y} {p : Y ⟶ S}
    [LocallyOfFiniteType f] [LocallyOfFiniteType p] {r e : ℕ}
    (α : Family f r) (β : Family p e) :
    comp α β =
      FiberCycleFamily.reindex (Int.natCast_add r e).symm
        (CyclesOnFibers.comp α β) := sorry

end AlgebraicGeometry.RelativeCycle

