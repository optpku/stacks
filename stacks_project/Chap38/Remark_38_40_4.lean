module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.CohomologyTorDimension
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/- Remark 38.40.4 (1): in a bounded finite-locally-free representative of `E`, every
differential image and every cycle object is finite locally free when all cohomology sheaves
of `E` are perfect of Tor dimension at most one. -/
@[stacks 0F8J]
#check (AlgebraicGeometry.Scheme.ModuleDerived.cyclesAndBoundaries_finiteLocallyFree :
  ∀ {X : Scheme.{u}} (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (K : _root_.CochainComplex X.Modules ℤ) (e : E ≅ DerivedCategory.Q.obj K)
    (hE : RingedSpace.ModuleDerived.IsPerfect E)
    (hK : SheafOfModules.CochainComplex.IsBoundedFiniteLocallyFree K)
    (hCohomologyPerfect : ∀ i : ℤ,
      SheafOfModules.IsPerfect (RingedSpace.ModuleDerived.cohomologySheaf E i))
    (hCohomologyTor : ∀ i : ℤ, RingedSpace.ModuleHasTorDimensionLE
      (RingedSpace.ModuleDerived.cohomologySheaf E i) 1),
    ∀ i : ℤ, SheafOfModules.IsFiniteLocallyFree (image (K.d i (i + 1))) ∧
      SheafOfModules.IsFiniteLocallyFree (K.cycles i))

/- Remark 38.40.4 (2): the canonical upper truncations of the representative and the
quotients of adjacent truncations are bounded complexes of finite locally free modules. -/
@[stacks 0F8J]
#check (AlgebraicGeometry.Scheme.ModuleDerived.truncLE_finiteLocallyFree :
  ∀ {X : Scheme.{u}} (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (K : _root_.CochainComplex X.Modules ℤ) (e : E ≅ DerivedCategory.Q.obj K)
    (hE : RingedSpace.ModuleDerived.IsPerfect E)
    (hK : SheafOfModules.CochainComplex.IsBoundedFiniteLocallyFree K)
    (hCohomologyPerfect : ∀ i : ℤ,
      SheafOfModules.IsPerfect (RingedSpace.ModuleDerived.cohomologySheaf E i))
    (hCohomologyTor : ∀ i : ℤ, RingedSpace.ModuleHasTorDimensionLE
      (RingedSpace.ModuleDerived.cohomologySheaf E i) 1),
    ∀ k : ℤ,
      SheafOfModules.CochainComplex.IsBoundedFiniteLocallyFree (K.truncLE k) ∧
        SheafOfModules.CochainComplex.IsBoundedFiniteLocallyFree
          (cokernel (K.truncLEStep k)))

/- Remark 38.40.4 (3): the cokernel sequence of adjacent upper truncations is short exact,
and its quotient represents the degree-`k` cohomology of `E` placed in degree `k`. -/
@[stacks 0F8J]
#check (AlgebraicGeometry.Scheme.ModuleDerived.truncationStep_representsCohomology :
  ∀ {X : Scheme.{u}} (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (K : _root_.CochainComplex X.Modules ℤ) (e : E ≅ DerivedCategory.Q.obj K)
    (hE : RingedSpace.ModuleDerived.IsPerfect E)
    (hK : SheafOfModules.CochainComplex.IsBoundedFiniteLocallyFree K)
    (hCohomologyPerfect : ∀ i : ℤ,
      SheafOfModules.IsPerfect (RingedSpace.ModuleDerived.cohomologySheaf E i))
    (hCohomologyTor : ∀ i : ℤ, RingedSpace.ModuleHasTorDimensionLE
      (RingedSpace.ModuleDerived.cohomologySheaf E i) 1),
    ∀ k : ℤ, (ShortComplex.cokernelSequence (K.truncLEStep k)).ShortExact ∧
      IsIsomorphic (DerivedCategory.Q.obj (cokernel (K.truncLEStep k)))
        ((DerivedCategory.singleFunctor X.Modules k).obj
          (RingedSpace.ModuleDerived.cohomologySheaf E k)))
