module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily

universe u

open AlgebraicGeometry

/- Compatibility bridge for existing consumers of the fibre-cycle family API. -/
#check (AlgebraicGeometry.Scheme.Hom.FiberCycleFamily :
  {X S : Scheme.{u}} → (f : X ⟶ S) → (k : ℤ) → Type u)
