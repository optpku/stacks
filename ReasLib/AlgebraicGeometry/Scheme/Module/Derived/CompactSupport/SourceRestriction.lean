/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CompactSupport.SourceNormalization

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalClosed
open RingedSpace.ModuleDerived.KFlat
open DerivedCategory.Bounded.CohomologyIn
open scoped DerivedCategory.CohomologyIn
noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport
variable {k : Type u} [Field k] {X U U' : Scheme.{u}}
variable [IsNoetherian X] [IsNoetherian U] [IsNoetherian U']
variable [HomotopyTensorDescends X.toRingedSpace] [TensorDescends X.toRingedSpace]
variable [IsLocalization X.toRingedSpace]
variable [HomotopyTensorDescends U.toRingedSpace] [TensorDescends U.toRingedSpace]
variable [IsLocalization U.toRingedSpace]
variable [HomotopyTensorDescends U'.toRingedSpace] [TensorDescends U'.toRingedSpace]
variable [IsLocalization U'.toRingedSpace]
variable [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
variable [MonoidalClosed (RingedSpace.ModuleDerived U.toRingedSpace)]
variable [MonoidalClosed (RingedSpace.ModuleDerived U'.toRingedSpace)]
variable (q : X ⟶ Spec (CommRingCat.of k)) [IsProper q]
variable (j : U ⟶ X) (i : U' ⟶ U) [IsOpenImmersion j] [IsOpenImmersion i]

/-- Restrict the literal source dual using the canonical pullback/RHom map,
the bounded restriction comparison, and the specified q!O compositor. -/
def sourceDualRestrictionComparison
    (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]) :
    (RingedSpace.modulePullbackDerived i.toShHom).obj (normalizedSourceDual q j K).obj.obj ⟶
      (normalizedSourceDual q (i ≫ j) ((DeligneSystem.restriction i).obj K)).obj.obj :=
  -- Local instance justification (defeq pin): use the constructed opens-site monoidal pullback with no additional caller-supplied data.
  letI := RingedSpace.modulePullbackDerived.opensSiteMonoidal i.toShHom
  RingedSpace.modulePullbackDerived.InternalHom.comparison i.toShHom K.obj.obj
      (openDualizing q j) ≫
    (preIso ((DeligneSystem.restrictionAmbientIso i).symm.app K)).hom.app
      ((RingedSpace.modulePullbackDerived i.toShHom).obj (openDualizing q j)) ≫
    (ihom ((DeligneSystem.restriction i).obj K).obj.obj).map
      (openDualizingRestrictionIso q j i).hom

/-- The specified source-dual restriction comparison is invertible for open immersions. -/
theorem sourceDualRestrictionComparison_isIso
    (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]) :
    IsIso (sourceDualRestrictionComparison q j i K) := sorry

/-- The bounded coherent comparison is the fully faithful lift of the actual
ambient restriction/RHom comparison. -/
def sourceDualRestrictionIso (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]) :
    (DeligneSystem.restriction i).obj (normalizedSourceDual q j K) ≅
      normalizedSourceDual q (i ≫ j) ((DeligneSystem.restriction i).obj K) :=
  (ambient (SheafOfModules.isCoherent U'.ringCatSheaf)).preimageIso
    ((DeligneSystem.restrictionAmbientIso i).app (normalizedSourceDual q j K) ≪≫
      @asIso _ _ _ _ (sourceDualRestrictionComparison q j i K)
        (sourceDualRestrictionComparison_isIso q j i K))

/-- The right vertical map is the canonical extension-by-zero restriction,
after the specified identification of the restricted source dual. -/
def normalizedCompactRestriction
    (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]) (d : ℤ) :
    cohomology q (DeligneSystem.boundedTower (i ≫ j) (DeligneSystem.extension (i ≫ j)
      (normalizedSourceDual q (i ≫ j) ((DeligneSystem.restriction i).obj K)))) d ⟶
      cohomology q (DeligneSystem.boundedTower j (DeligneSystem.extension j
        (normalizedSourceDual q j K))) d :=
  Pro.ModuleLimit.map (Cohomology.overFieldFunctor q d)
    ((DeligneSystem.extensionByZero (i ≫ j)).map (sourceDualRestrictionIso q j i K).inv ≫
      DeligneSystem.canonicalOpenRestriction i j (normalizedSourceDual q j K))

/-- Ordinary restriction on the original schemes is induced by the actual
derived adjunction unit, with only associativity and bounded restriction transports. -/
def normalizedOrdinaryRestriction
    (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]) (d : ℤ) :
    (Cohomology.globalCohomologyOverField (j ≫ q) d).obj K.obj.obj ⟶
      (Cohomology.globalCohomologyOverField ((i ≫ j) ≫ q) d).obj
        ((DeligneSystem.restriction i).obj K).obj.obj :=
  IdealDuality.geometricOrdinaryRestriction (j ≫ q) i K.obj.obj d ≫
    eqToHom (congrArg
      (fun p ↦ (Cohomology.globalCohomologyOverField p d).obj
        ((RingedSpace.modulePullbackDerived i.toShHom).obj K.obj.obj))
      (Category.assoc i j q).symm) ≫
    (Cohomology.globalCohomologyOverField ((i ≫ j) ≫ q) d).map
      ((DeligneSystem.restrictionAmbientIso i).inv.app K)

variable [DerivedCategory.DerivedTensor.Bifunctor.Has (C := RingedSpace.Modules X.toRingedSpace)]
variable [DerivedCategory.DerivedTensor.Bifunctor.Has (C := X.Modules)]

/-- The source-direction duality square on a common proper compactification,
with each horizontal constructed from the normalized trace and actual realization.
No compatibility between chosen extensions is a premise. -/
theorem sourceDuality_openRestriction
    (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf])
    (I I' : X.IdealSheafData) (hI : I.openComplement = j.opensRange)
    (hI' : I'.openComplement = (i ≫ j).opensRange) (d : ℤ) :
    (normalizedCompactRestriction q j i K (-d)).hom.comp
        (sourceDuality q (i ≫ j) ((DeligneSystem.restriction i).obj K) I' hI' d).toLinearMap =
      (sourceDuality q j K I hI d).toLinearMap.comp
        (normalizedOrdinaryRestriction q j i K d).hom.dualMap := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport
