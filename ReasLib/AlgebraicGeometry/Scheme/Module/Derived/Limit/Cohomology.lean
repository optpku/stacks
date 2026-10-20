module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Limit.Cohomology
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Limit.Single
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.Adjunction
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic
public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler.Epi

/-!
# Cohomology of epimorphic inverse systems of derived quasicoherent modules

Degreewise epimorphic transitions identify the cohomology of a derived inverse limit with the
ordinary inverse limit of the cohomology sheaves.  The latter is again a homotopy limit and is
acyclic on affine opens in positive degrees.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

variable {X : Scheme.{u}}

/-- For a sequential system with quasicoherent cohomology and epimorphic cohomology transitions,
the cohomology sheaf of a derived limit is isomorphic to the inverse limit of the cohomology
sheaves. -/
theorem cohomologySheaf_iso_limit_of_epi
    (Ksys : SequentialInverseSystem
      (DerivedCategory.CohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)))
    (K : RingedSpace.ModuleDerived X.toRingedSpace)
    (hK : IsDerivedLimit
      (Ksys ⋙ (DerivedCategory.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).ι) K)
    (h_epi : ∀ (q : ℤ) (n : ℕ), Epi
      (SequentialInverseSystem.transitionMap
        (Ksys ⋙ (DerivedCategory.cohomologyIn
          (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).ι ⋙
            DerivedCategory.homologyFunctor X.toRingedSpace.Modules q)
        (Nat.le_succ n)))
    (q : ℤ) :
    IsIsomorphic (RingedSpace.ModuleDerived.cohomologySheaf K q)
      (limit (Ksys ⋙ (DerivedCategory.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).ι ⋙
          DerivedCategory.homologyFunctor X.toRingedSpace.Modules q)) := sorry

/-- For such a sequential system, the ordinary inverse limit of the degree-`q` cohomology
sheaves, placed in degree zero, is a homotopy limit of their degree-zero tower. -/
theorem cohomologySheaf_limit_isOf_of_epi
    (Ksys : SequentialInverseSystem
      (DerivedCategory.CohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)))
    (K : RingedSpace.ModuleDerived X.toRingedSpace)
    (hK : IsDerivedLimit
      (Ksys ⋙ (DerivedCategory.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).ι) K)
    (h_epi : ∀ (q : ℤ) (n : ℕ), Epi
      (SequentialInverseSystem.transitionMap
        (Ksys ⋙ (DerivedCategory.cohomologyIn
          (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).ι ⋙
            DerivedCategory.homologyFunctor X.toRingedSpace.Modules q)
        (Nat.le_succ n)))
    (q : ℤ) :
    HomotopyLimit.IsOf
      ((Ksys ⋙ (DerivedCategory.cohomologyIn
          (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).ι ⋙
            DerivedCategory.homologyFunctor X.toRingedSpace.Modules q) ⋙
        DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ))
      ((DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj
        (limit (Ksys ⋙ (DerivedCategory.cohomologyIn
          (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).ι ⋙
            DerivedCategory.homologyFunctor X.toRingedSpace.Modules q))) := sorry

/-- For such a sequential system, the inverse limit of the degree-`q` cohomology sheaves has
zero positive cohomology on every affine open. -/
theorem cohomologySheaf_limit_higherCohomology_isZero_of_epi
    (Ksys : SequentialInverseSystem
      (DerivedCategory.CohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)))
    (K : RingedSpace.ModuleDerived X.toRingedSpace)
    (hK : IsDerivedLimit
      (Ksys ⋙ (DerivedCategory.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).ι) K)
    (h_epi : ∀ (q : ℤ) (n : ℕ), Epi
      (SequentialInverseSystem.transitionMap
        (Ksys ⋙ (DerivedCategory.cohomologyIn
          (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).ι ⋙
            DerivedCategory.homologyFunctor X.toRingedSpace.Modules q)
        (Nat.le_succ n)))
    (q : ℤ) (U : X.Opens) (hU : IsAffineOpen U) (p : ℕ) (hp : 0 < p) :
    IsZero
      (((SheafOfModules.toSheaf X.toRingedSpace.ringCatSheaf).obj
        (limit (Ksys ⋙ (DerivedCategory.cohomologyIn
          (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).ι ⋙
            DerivedCategory.homologyFunctor X.toRingedSpace.Modules q))).H' p U) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh

end
