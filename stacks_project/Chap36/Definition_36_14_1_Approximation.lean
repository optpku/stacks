/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PerfectApproximation

universe u

/- Compatibility bridge for files that imported the earlier source-side approximation module. -/
#check
  (AlgebraicGeometry.Scheme.HasPerfectApproximation :
    {X : AlgebraicGeometry.Scheme.{u}} →
      (T : TopologicalSpace.Closeds X) →
      (E : CategoryTheory.DerivedCategory.CohomologyIn
        (AlgebraicGeometry.RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)) →
      (m : ℤ) → Prop)
