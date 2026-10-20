module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import ReasLib.AlgebraicGeometry.RelativeCycle
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.Effective
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily.Operations

@[expose] public section

open AlgebraicGeometry CategoryTheory

open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

open Scheme.Hom

/-- Over a locally Noetherian base, a relative cycle of nonnegative degree for a
locally finite type morphism is effective if and only if its base change along
a surjective morphism is effective. -/
theorem isEffective_iff_baseChange {X S S' : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ)
    (α : CyclesOnFibers f r) (hα : RelativeCycle.IsRelative α)
    (g : S' ⟶ S) [Surjective g] :
    Scheme.Hom.CyclesOnFibers.IsEffective α ↔
      Scheme.Hom.CyclesOnFibers.IsEffective
        (Scheme.Hom.FiberCycleFamily.baseChange (IsPullback.of_hasPullback f g) α) := sorry

end AlgebraicGeometry
