/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily

universe u

open AlgebraicGeometry

/- Compatibility bridge for existing consumers of the fibre-cycle family API. -/
#check (AlgebraicGeometry.Scheme.Hom.FiberCycleFamily :
  {X S : Scheme.{u}} → (f : X ⟶ S) → (k : ℤ) → Type u)
