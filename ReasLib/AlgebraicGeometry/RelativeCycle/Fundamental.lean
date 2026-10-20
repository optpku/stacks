module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily.Fundamental
public import ReasLib.AlgebraicGeometry.RelativeCycle.ClosedSubscheme.Flat

/-!
# Fundamental relative cycles

A flat morphism of fixed relative dimension over a locally Noetherian base
has a fundamental fibre-cycle family that is a relative cycle.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The associated fibre-cycle family of the identity closed subscheme is a
relative `r`-cycle when `f` is flat of relative dimension `r` and `S` is
locally Noetherian. -/
theorem closedSubschemeFiberCycleFamily_bot_isRelative {X S : Scheme.{u}}
    (f : X ⟶ S) [IsLocallyNoetherian S] (r : ℕ) [Flat f] [RelativeDimension f r] :
    RelativeCycle.IsRelative
      (closedSubschemeFiberCycleFamily f (⊥ : X.IdealSheafData) r
        (fiberClosedSubschemeDimensionLE_bot f r)) := sorry

/-- The associated fibre-cycle family of the identity closed subscheme lies in
`z(X/S, r)` when `f` is flat of relative dimension `r` and `S` is locally
Noetherian. -/
theorem closedSubschemeFiberCycleFamily_bot_mem_group {X S : Scheme.{u}}
    (f : X ⟶ S) [IsLocallyNoetherian S] (r : ℕ) [Flat f] [RelativeDimension f r] :
    closedSubschemeFiberCycleFamily f (⊥ : X.IdealSheafData) r
        (fiberClosedSubschemeDimensionLE_bot f r) ∈
      RelativeCycle.group f r := sorry

end AlgebraicGeometry.Scheme.Hom
