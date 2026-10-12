/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Perfect.LocallyFree
public import ReasLib.Algebra.Homology.CochainComplex.Filtration.Truncation.Step
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived

/-- In a bounded finite-locally-free complex representing a perfect derived module whose
cohomology sheaves are perfect of Tor dimension at most one, every differential image and
cycle object is finite locally free. -/
theorem cyclesAndBoundaries_finiteLocallyFree {X : Scheme.{u}}
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (K : _root_.CochainComplex X.Modules ℤ) (e : E ≅ DerivedCategory.Q.obj K)
    (hE : RingedSpace.ModuleDerived.IsPerfect E)
    (hK : SheafOfModules.CochainComplex.IsBoundedFiniteLocallyFree K)
    (hCohomologyPerfect : ∀ i : ℤ,
      SheafOfModules.IsPerfect (RingedSpace.ModuleDerived.cohomologySheaf E i))
    (hCohomologyTor : ∀ i : ℤ, RingedSpace.ModuleHasTorDimensionLE
      (RingedSpace.ModuleDerived.cohomologySheaf E i) 1) :
    ∀ i : ℤ, SheafOfModules.IsFiniteLocallyFree (image (K.d i (i + 1))) ∧
      SheafOfModules.IsFiniteLocallyFree (K.cycles i) := sorry

/-- The canonical upper truncations of such a representative and the cokernels of adjacent
truncation maps are bounded complexes of finite locally free modules. -/
theorem truncLE_finiteLocallyFree {X : Scheme.{u}}
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (K : _root_.CochainComplex X.Modules ℤ) (e : E ≅ DerivedCategory.Q.obj K)
    (hE : RingedSpace.ModuleDerived.IsPerfect E)
    (hK : SheafOfModules.CochainComplex.IsBoundedFiniteLocallyFree K)
    (hCohomologyPerfect : ∀ i : ℤ,
      SheafOfModules.IsPerfect (RingedSpace.ModuleDerived.cohomologySheaf E i))
    (hCohomologyTor : ∀ i : ℤ, RingedSpace.ModuleHasTorDimensionLE
      (RingedSpace.ModuleDerived.cohomologySheaf E i) 1) :
    ∀ k : ℤ,
      SheafOfModules.CochainComplex.IsBoundedFiniteLocallyFree (K.truncLE k) ∧
        SheafOfModules.CochainComplex.IsBoundedFiniteLocallyFree
          (cokernel (K.truncLEStep k)) := sorry

/-- The cokernel sequence of adjacent upper truncations is short exact, and its quotient
represents the corresponding cohomology sheaf placed in its cochain degree. -/
theorem truncationStep_representsCohomology {X : Scheme.{u}}
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (K : _root_.CochainComplex X.Modules ℤ) (e : E ≅ DerivedCategory.Q.obj K)
    (hE : RingedSpace.ModuleDerived.IsPerfect E)
    (hK : SheafOfModules.CochainComplex.IsBoundedFiniteLocallyFree K)
    (hCohomologyPerfect : ∀ i : ℤ,
      SheafOfModules.IsPerfect (RingedSpace.ModuleDerived.cohomologySheaf E i))
    (hCohomologyTor : ∀ i : ℤ, RingedSpace.ModuleHasTorDimensionLE
      (RingedSpace.ModuleDerived.cohomologySheaf E i) 1) :
    ∀ k : ℤ, (ShortComplex.cokernelSequence (K.truncLEStep k)).ShortExact ∧
      IsIsomorphic (DerivedCategory.Q.obj (cokernel (K.truncLEStep k)))
        ((DerivedCategory.singleFunctor X.Modules k).obj
          (RingedSpace.ModuleDerived.cohomologySheaf E k)) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived
