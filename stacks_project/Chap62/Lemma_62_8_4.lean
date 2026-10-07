module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import stacks_project.Chap62.Lemma_62_6_6_Relative
public import stacks_project.Chap62.Lemma_62_7_3_Operations
public import stacks_project.Chap62.Lemma_62_8_3_RelativeCycle

@[expose] public section

open AlgebraicGeometry CategoryTheory

open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

open Scheme.Hom

/-- Lemma 62.8.4: if `S` is locally Noetherian and `f : X ⟶ S` is locally of
finite type, then a relative `r`-cycle `α` on `X / S` is effective if and only
if its base change along a surjective morphism `g : S' ⟶ S` is effective. -/
@[stacks 0H5U]
theorem isEffective_iff_baseChange {X S S' : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ)
    (α : CyclesOnFibers f r) (hα : RelativeCycle.IsRelative α)
    (g : S' ⟶ S) [Surjective g] :
    α.IsEffective ↔ (α.baseChange g).IsEffective := sorry

end AlgebraicGeometry
