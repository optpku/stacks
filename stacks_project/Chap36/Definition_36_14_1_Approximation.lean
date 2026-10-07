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
