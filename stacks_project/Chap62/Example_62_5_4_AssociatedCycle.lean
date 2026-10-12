/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily.ClosedSubscheme

universe u

open CategoryTheory AlgebraicGeometry

/- Compatibility bridge for existing consumers of the associated fibre-cycle family API. -/
#check (AlgebraicGeometry.Scheme.Hom.closedSubschemeFiberCycleFamily :
  {X S : Scheme.{u}} → (f : X ⟶ S) → [LocallyOfFiniteType f] →
    (Z : X.IdealSheafData) → (r : ℕ) →
    f.fiberClosedSubschemeDimensionLE Z r → f.FiberCycleFamily (r : ℤ))
