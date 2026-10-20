/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.NormalizedPairing
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RightAdjoint
public import ReasLib.CategoryTheory.Monoidal.Closed.Triangulated

/-!
# A specified Ext to RHom-cohomology comparison

The map is obtained by currying and the derived global-sections unit, retaining
the scalar structure induced by the scheme's morphism to the ground field.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open RingedSpace.ModuleDerived.KFlat Scheme.Hom
open Scheme.DerivedQCoh.ProperDualizingComplex
open scoped DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.Cohomology

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The actual scalar-restricted derived global-sections cohomology functor. -/
def globalCohomologyOverField (p : X ⟶ Spec (CommRingCat.of k)) (n : ℤ) :
    RingedSpace.ModuleDerived X.toRingedSpace ⥤ ModuleCat.{u} k :=
  RingedSpace.moduleDerivedGlobalSections X.toRingedSpace ⋙
    ModuleCat.derivedRestrictionOfScalars p.globalSectionsMap ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} k) n

/-- The ground-field unit in sections of the structure sheaf, with the actual
scalar action induced by p. -/
def groundFieldToSections (p : X ⟶ Spec (CommRingCat.of k)) :
    ModuleCat.of k k ⟶
      (ModuleCat.restrictScalars.{u} p.globalSectionsMap).obj
        ((RingedSpace.moduleGlobalSectionsFunctor X.toRingedSpace).obj
          (SheafOfModules.unit X.ringCatSheaf)) :=
  let T : ModuleCat.{u} k :=
    (ModuleCat.restrictScalars.{u} p.globalSectionsMap).obj
      ((RingedSpace.moduleGlobalSectionsFunctor X.toRingedSpace).obj
        (SheafOfModules.unit X.ringCatSheaf))
  @ModuleCat.ofHom k _ k T _ _ T.isAddCommGroup T.isModule
    ({
      toFun := fun a ↦ p.globalSectionsMap a
      map_add' := sorry
      map_smul' := sorry } : k →ₗ[k] T)

/-- The ground-field unit in degree-zero derived sections of O_X. -/
def groundFieldToDerivedSections (p : X ⟶ Spec (CommRingCat.of k)) :
    ModuleCat.of k k ⟶
      (globalCohomologyOverField p 0).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf)) :=
  let R : ModuleCat.{u} (Scheme.globalSectionsRing X) ⥤ ModuleCat.{u} k :=
    ModuleCat.restrictScalars.{u} p.globalSectionsMap
  let M := SheafOfModules.unit X.ringCatSheaf
  groundFieldToSections p ≫ R.map (globalSectionsToHomologyZero X M) ≫
    (@exactFunctor_homology_iso_mapDerivedCategory
      (ModuleCat.{u} (Scheme.globalSectionsRing X)) (ModuleCat.{u} k)
      _ _ (ModuleCat.hasDerivedCategory (Scheme.globalSectionsRing X))
      _ _ (ModuleCat.hasDerivedCategory k) R _ _ _
      ((RingedSpace.moduleDerivedGlobalSections X.toRingedSpace).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj M)) 0).hom

variable [HomotopyTensorDescends X.toRingedSpace] [TensorDescends X.toRingedSpace]
variable [IsLocalization X.toRingedSpace]
variable [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]

/-- The tensor unit in the K-flat model is the structure sheaf in degree zero. -/
def structureSheafTensorUnitIso :
    (DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf) ≅
      𝟙_ (RingedSpace.ModuleDerived X.toRingedSpace) :=
  (DerivedCategory.singleFunctor X.Modules 0).mapIso
      (RingedSpace.unitIsoTensorUnit X.toRingedSpace) ≪≫
    (DerivedCategory.KFlat.mapUnitIso
      (C := RingedSpace.Modules X.toRingedSpace)).symm

/-- Currying a degree-n derived morphism produces the specified degree-zero
cohomology class of RHom(L,M[n]). -/
def extToRHomClass (p : X ⟶ Spec (CommRingCat.of k))
    (L M : RingedSpace.ModuleDerived X.toRingedSpace) (n : ℤ)
    (f : DerivedExt.value p L M n) :
    (globalCohomologyOverField p 0).obj ((ihom L).obj (M⟦n⟧)) :=
  ((groundFieldToDerivedSections p) ≫
    (globalCohomologyOverField p 0).map
      (structureSheafTensorUnitIso.hom ≫ curry' f)).hom 1

/-- Additivity follows from currying, the derived functor and evaluation at 1. -/
theorem extToRHomClass_add (p : X ⟶ Spec (CommRingCat.of k))
    (L M : RingedSpace.ModuleDerived X.toRingedSpace) (n : ℤ)
    (f g : DerivedExt.value p L M n) :
    extToRHomClass p L M n (f + g) =
      extToRHomClass p L M n f + extToRHomClass p L M n g := sorry

/-- The comparison respects the scalar action from the same structure map p. -/
theorem extToRHomClass_smul (p : X ⟶ Spec (CommRingCat.of k))
    (L M : RingedSpace.ModuleDerived X.toRingedSpace) (n : ℤ)
    (a : k) (f : DerivedExt.value p L M n) :
    extToRHomClass p L M n (a • f) = a • extToRHomClass p L M n f := sorry

/-- The linear comparison has the explicit currying and sections-unit map as
its underlying function. -/
def extToRHom (p : X ⟶ Spec (CommRingCat.of k))
    (L M : RingedSpace.ModuleDerived X.toRingedSpace) (n : ℤ) :
    DerivedExt.value p L M n →ₗ[k]
      (globalCohomologyOverField p 0).obj ((ihom L).obj (M⟦n⟧)) where
  toFun := extToRHomClass p L M n
  map_add' := extToRHomClass_add p L M n
  map_smul' := extToRHomClass_smul p L M n

/-- The specified comparison is bijective: derived global sections of RHom
represent derived morphisms. This concerns this map, not an unspecified iso. -/
theorem extToRHom_bijective (p : X ⟶ Spec (CommRingCat.of k))
    (L M : RingedSpace.ModuleDerived X.toRingedSpace) (n : ℤ) :
    Function.Bijective (extToRHom p L M n) := sorry

/-- The inverse of the specified map gives the canonical RHom-cohomology to
Ext identification, in the degree-zero shifted-target presentation. -/
def rhomToExtEquiv (p : X ⟶ Spec (CommRingCat.of k))
    (L M : RingedSpace.ModuleDerived X.toRingedSpace) (n : ℤ) :
    (globalCohomologyOverField p 0).obj ((ihom L).obj (M⟦n⟧)) ≃ₗ[k]
      DerivedExt.value p L M n :=
  (LinearEquiv.ofBijective (extToRHom p L M n) (extToRHom_bijective p L M n)).symm

/-- The fixed-left tensor shift structure is transported from the actual
fixed-right derived tensor via its K-flat comparison and the symmetry. -/
@[implicit_reducible] def tensorLeftShift (L : RingedSpace.ModuleDerived X.toRingedSpace) :
    (tensorLeft L).CommShift ℤ :=
  let model :=
    @Scheme.ModuleDerived.ProjectionFormula.kFlatTensorModel X
      (Scheme.ModuleDerived.ProjectionFormula.hasKFlatResolutions X)
      (inferInstanceAs (HomotopyTensorDescends X.toRingedSpace))
      (inferInstanceAs (TensorDescends X.toRingedSpace))
      (inferInstanceAs (TensorDescends X.toRingedSpace))
      (inferInstanceAs (IsLocalization X.toRingedSpace))
      (inferInstanceAs (IsLocalization X.toRingedSpace))
      (Scheme.ModuleDerived.ProjectionFormula.homotopyLocalization_isLocalization X)
  -- Local instance justification (defeq pin): use the canonical fixed-right derived tensor shift when transporting along its specified K-flat comparison.
  letI := DerivedCategory.DerivedTensor.Right.commShift L
  let e := @DerivedCategory.DerivedTensor.Right.Monoidal.Model.functorIsoTensorRight
    (RingedSpace.Modules X.toRingedSpace) _ _ _ _ _ _
    (RingedSpace.ModuleDerived.monoidalCategory X.toRingedSpace) model L _
  Functor.CommShift.ofIso (e ≪≫ (BraidedCategory.tensorLeftIsoTensorRight L).symm) ℤ

/-- Internal Hom inherits its shift comparison as the right adjoint of the
specified tensor shift, fixing the normalization of the degree conversion. -/
@[implicit_reducible] def ihomShift (L : RingedSpace.ModuleDerived X.toRingedSpace) :
    (ihom L).CommShift ℤ :=
  -- Local instance justification (defeq pin): the right-adjoint shift must be induced by this canonical tensor comparison, not an unrelated shift choice.
  letI := tensorLeftShift L
  (ihom.adjunction L).rightAdjointCommShift ℤ

/-- The canonical shift comparison for the scalar-restricted global-sections
functor is the composition of its existing derived-functor shift structures. -/
@[implicit_reducible] def globalSectionsShift (p : X ⟶ Spec (CommRingCat.of k)) :
    (RingedSpace.moduleDerivedGlobalSections X.toRingedSpace ⋙
      ModuleCat.derivedRestrictionOfScalars p.globalSectionsMap).CommShift ℤ :=
  Functor.CommShift.comp _ _

/-- Degree-zero RHom with shifted target is identified with degree-n RHom
cohomology by the specified adjunction shift, derived sections shift, and
homology shift comparison. -/
def rhomDegreeIso (p : X ⟶ Spec (CommRingCat.of k))
    (L M : RingedSpace.ModuleDerived X.toRingedSpace) (n : ℤ) :
    (globalCohomologyOverField p 0).obj ((ihom L).obj (M⟦n⟧)) ≅
      (globalCohomologyOverField p n).obj ((ihom L).obj M) :=
  let G := RingedSpace.moduleDerivedGlobalSections X.toRingedSpace ⋙
    ModuleCat.derivedRestrictionOfScalars p.globalSectionsMap
  -- Local instance justification (defeq pin): bind the actual adjunction-derived internal-Hom shift used in this degree conversion.
  letI := ihomShift L
  -- Local instance justification (defeq pin): bind the composed derived global-sections shift used in the same degree conversion.
  letI := globalSectionsShift p
  (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).mapIso
      (G.mapIso (((ihom L).commShiftIso n).app M) ≪≫
        (G.commShiftIso n).app ((ihom L).obj M)) ≪≫
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).shiftIso n 0 n
      (add_zero n)).app (G.obj ((ihom L).obj M))

/-- The actual degree-n RHom cohomology is canonically identified with
degree-n Ext, with no comparison isomorphism supplied by the caller. -/
def rhomCohomologyExtEquiv (p : X ⟶ Spec (CommRingCat.of k))
    (L M : RingedSpace.ModuleDerived X.toRingedSpace) (n : ℤ) :
    (globalCohomologyOverField p n).obj ((ihom L).obj M) ≃ₗ[k]
      DerivedExt.value p L M n :=
  (rhomDegreeIso p L M n).symm.toLinearEquiv.trans (rhomToExtEquiv p L M n)

/-- The specified comparison is contravariantly natural in the RHom source;
the cohomology map is induced by the actual internal-Hom precomposition. -/
theorem rhomCohomologyExtEquiv_precomp (p : X ⟶ Spec (CommRingCat.of k))
    {L L' M : RingedSpace.ModuleDerived X.toRingedSpace} (f : L' ⟶ L) (n : ℤ)
    (x : (globalCohomologyOverField p n).obj ((ihom L).obj M)) :
    rhomCohomologyExtEquiv p L' M n
        (((globalCohomologyOverField p n).map ((MonoidalClosed.pre f).app M)).hom x) =
      f ≫ rhomCohomologyExtEquiv p L M n x := sorry

/-- The specified comparison is covariantly natural in the RHom target,
with the target map shifted by exactly the Ext degree. -/
theorem rhomCohomologyExtEquiv_postcomp (p : X ⟶ Spec (CommRingCat.of k))
    {L M M' : RingedSpace.ModuleDerived X.toRingedSpace} (f : M ⟶ M') (n : ℤ)
    (x : (globalCohomologyOverField p n).obj ((ihom L).obj M)) :
    rhomCohomologyExtEquiv p L M' n
        (((globalCohomologyOverField p n).map ((ihom L).map f)).hom x) =
      rhomCohomologyExtEquiv p L M n x ≫ (shiftFunctor _ n).map f := sorry

/-- The degree-n proper RHom-cohomology pairing is the constructed RHom/Ext
map followed by the adjunction pairing normalized by the base structure-sheaf
unit. There is no independently chosen horizontal comparison. -/
def properRHomPairing (q : X ⟶ Spec (CommRingCat.of k)) [IsProper q]
    (L : Scheme.DerivedQCoh X) (n : ℤ) :
    (globalCohomologyOverField q n).obj
        ((ihom L.obj).obj (Scheme.DerivedQCoh.properDualizingComplex q).obj) →ₗ[k]
      Module.Dual k (cohomologyOverField q L (-n)) :=
  (normalizedPairing q n L).comp
    (rhomCohomologyExtEquiv q L.obj (Scheme.DerivedQCoh.properDualizingComplex q).obj n).toLinearMap

/-- Evaluation of the proper pairing is the specified RHom/Ext conversion
followed by the normalized adjunction pairing. -/
theorem properRHomPairing_apply (q : X ⟶ Spec (CommRingCat.of k)) [IsProper q]
    (L : Scheme.DerivedQCoh X) (n : ℤ)
    (x : (globalCohomologyOverField q n).obj
      ((ihom L.obj).obj (Scheme.DerivedQCoh.properDualizingComplex q).obj)) :
    properRHomPairing q L n x =
      normalizedPairing q n L
        (rhomCohomologyExtEquiv q L.obj
          (Scheme.DerivedQCoh.properDualizingComplex q).obj n x) := sorry

open DerivedCategory.TStructure

/-- The concrete proper tensor-stage pairing. It maps the source's compact
tensor stage through tensor–RHom, the specified RHom/Ext equivalence, and
the unit-normalized adjunction pairing. All three arrows are constructed. -/
def properTensorStagePairing [IsLocallyNoetherian X]
    (q : X ⟶ Spec (CommRingCat.of k)) [IsProper q]
    (I M : Scheme.DerivedQCoh X)
    (hI : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.ringCatSheaf) I.obj)
    (hIa : (t.minus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) I.obj)
    (hM : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.ringCatSheaf) M.obj)
    (hMb : (t.plus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) M.obj)
    (n : ℤ) :
    (globalCohomologyOverField q n).obj
        (((ihom M.obj).obj (Scheme.DerivedQCoh.properDualizingComplex q).obj) ⊗ I.obj) →ₗ[k]
      Module.Dual k (cohomologyOverField q (ordinaryStage I M hI hIa hM hMb) (-n)) :=
  (properRHomPairing q (ordinaryStage I M hI hIa hM hMb) n).comp
    ((globalCohomologyOverField q n).map
      (TensorRight.comparisonOf
        (inferInstance : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
        I.obj M.obj (Scheme.DerivedQCoh.properDualizingComplex q).obj)).hom

end AlgebraicGeometry.Scheme.ModuleDerived.Cohomology
