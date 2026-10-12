/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily.Hilbert

universe u

open CategoryTheory AlgebraicGeometry

/- Compatibility bridge for existing consumers of the Hilbert cycle-class API. -/
#check (AlgebraicGeometry.Scheme.Hom.hilbertCycleClass :
  {X S : Scheme.{u}} → (f : X ⟶ S) → [LocallyOfFiniteType f] →
    (r : ℕ) →
    FreeAbelianGroup (f.HilbertClosedSubscheme r) →+
      f.FiberCycleFamily (r : ℤ))
