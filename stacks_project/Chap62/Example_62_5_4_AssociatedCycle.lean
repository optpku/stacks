module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily.ClosedSubscheme

universe u

open CategoryTheory AlgebraicGeometry

/- Compatibility bridge for existing consumers of the associated fibre-cycle family API. -/
#check (AlgebraicGeometry.Scheme.Hom.closedSubschemeFiberCycleFamily :
  {X S : Scheme.{u}} → (f : X ⟶ S) → [LocallyOfFiniteType f] →
    (Z : X.IdealSheafData) → (r : ℕ) →
    f.fiberClosedSubschemeDimensionLE Z r → f.FiberCycleFamily (r : ℤ))
