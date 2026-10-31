/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.OverSections
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.IdealStalk
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Support
public import ReasLib.AlgebraicGeometry.RingedSpace.SectionSequence.Regularity

/-!
# Regular ideal sheaves on ringed spaces

This leaf owns local finite-sequence regularity conditions for ideal sheaves.
Its sectionwise ideal, stalk ideal, support, and finite-sequence criteria are
all supplied by reusable lower-level APIs.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits Opposite
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/-- The support of `𝒪_X / 𝓘`, for an ideal sheaf subobject `𝓘 ⊆ 𝒪_X`. -/
def idealQuotientSupport
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf)) : Set X :=
  moduleSupport (cokernel I.arrow)

/-- The quotient support is the module support of the cokernel of the ideal inclusion. -/
theorem idealQuotientSupport_def
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf)) :
    idealQuotientSupport I = moduleSupport (cokernel I.arrow) := rfl

/-- A point belongs to the quotient support precisely when its stalk ideal is proper. -/
theorem mem_idealQuotientSupport
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf)) (x : X) :
    x ∈ idealQuotientSupport I ↔ idealSheafStalkIdeal I x ≠ ⊤ := by
  change (¬ IsZero (TopCat.Presheaf.stalk (cokernel I.arrow).val.presheaf x)) ↔ _
  have hzero : IsZero (TopCat.Presheaf.stalk (cokernel I.arrow).val.presheaf x) ↔
      Epi (moduleStalkHom x I.arrow) := by
    calc
      _ ↔ IsZero (stalkModuleCat (cokernel I.arrow) x) :=
        AddCommGrpCat.isZero_iff_subsingleton.trans
          (ModuleCat.isZero_iff_subsingleton
            (M := stalkModuleCat (cokernel I.arrow) x)).symm
      _ ↔ IsZero (cokernel (moduleStalkHom x I.arrow)) :=
        (PreservesCokernel.iso (stalkModuleFunctor x) I.arrow).isZero_iff
      _ ↔ Epi (moduleStalkHom x I.arrow) :=
        (CategoryTheory.Preadditive.epi_iff_isZero_cokernel _).symm
  refine (not_congr hzero).trans (not_congr ?_)
  change Epi (moduleStalkHom x I.arrow) ↔
    LinearMap.range (idealSheafStalkToRing I x).hom = ⊤
  calc
    _ ↔ Function.Surjective (moduleStalkHom x I.arrow) := ModuleCat.epi_iff_surjective _
    _ ↔ Function.Surjective (idealSheafStalkToRing I x).hom :=
      (Equiv.comp_surjective (moduleStalkHom x I.arrow)
        (unitStalkLinearEquiv x).toEquiv).symm
    _ ↔ _ := LinearMap.range_eq_top.symm

/-- A local section of an ideal sheaf, viewed as a local section of the ambient structure sheaf.
-/
def idealSectionToRingSection
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf)) (U : Opens X)
    (s : (I : X.Modules).val.obj (op U)) :
    X.presheaf.obj (op U) :=
  SheafOfModules.unitSectionToRingSection U
    (SheafOfModules.Subobject.inclusionApp I (op U) s)

/-- The explicit sectionwise inclusion defining `idealSectionToRingSection`. -/
theorem idealSectionToRingSection_def
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf)) (U : Opens X)
    (s : (I : X.Modules).val.obj (op U)) :
    idealSectionToRingSection I U s =
      SheafOfModules.unitSectionToRingSection U
        (SheafOfModules.Subobject.inclusionApp I (op U) s) := rfl

/-- Passing from ideal-sheaf sections to structure-sheaf sections commutes with restriction. -/
theorem idealSectionToRingSection_restrict
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf))
    {U V : Opens X} (i : V ⟶ U) (s : (I : X.Modules).val.obj (op U)) :
    X.presheaf.map i.op (idealSectionToRingSection I U s) =
      idealSectionToRingSection I V (((I : X.Modules).val.map i.op).hom s) := by
  exact (PresheafOfModules.naturality_apply I.arrow.val i.op s).symm

/-- A finite ideal-section family generates `I` on `U` when the associated morphism from the
finite free sheaf to the restriction of `I` to `U` is an epimorphism. -/
def IsGeneratedByIdealSectionFamilyOn
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf))
    (U : Opens X) {r : ℕ} (f : Fin r → (I : X.Modules).val.obj (op U)) : Prop :=
  Epi ((SheafOfModules.freeHomEquiv (I := ULift.{u} (Fin r)) ((I : X.Modules).over U)).symm
    (fun i ↦ (SheafOfModules.sectionsOverEquiv (I : X.Modules) U).symm (f i.down)))

/-- Generation by a finite ideal-section family is the epimorphism condition for its associated
finite-free-sheaf morphism. -/
theorem isGeneratedByIdealSectionFamilyOn_iff
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf))
    (U : Opens X) {r : ℕ} (f : Fin r → (I : X.Modules).val.obj (op U)) :
    IsGeneratedByIdealSectionFamilyOn I U f ↔
      Epi ((SheafOfModules.freeHomEquiv
        (I := ULift.{u} (Fin r)) ((I : X.Modules).over U)).symm
          (fun i ↦
            (SheafOfModules.sectionsOverEquiv (I : X.Modules) U).symm (f i.down))) := Iff.rfl

/-- An ideal sheaf is locally generated near its quotient support by finite families satisfying
a prescribed finite-sequence condition. -/
def isLocallyGeneratedBySequencePredicate
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf))
    (P : ∀ {U : Opens X} {r : ℕ}, (Fin r → X.presheaf.obj (op U)) → Prop) : Prop :=
  ∀ x ∈ idealQuotientSupport I,
    ∃ (U : Opens X) (_ : x ∈ U) (r : ℕ) (f : Fin r → (I : X.Modules).val.obj (op U)),
      P (fun j ↦ idealSectionToRingSection I U (f j)) ∧
        IsGeneratedByIdealSectionFamilyOn I U f

/-- An ideal sheaf `𝓘 ⊆ 𝒪_X` is regular when near every point of
`Supp (𝒪_X / 𝓘)` it is generated by a finite regular sequence. -/
@[stacks 063D]
class IsRegularIdealSheaf
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf)) : Prop where
  /-- Near the quotient support, the ideal sheaf is generated by finite regular sequences. -/
  locallyGeneratedByRegularSequence :
    isLocallyGeneratedBySequencePredicate I
      (fun {_ _} f ↦ SectionSequence.IsRegular f)

/-- The local finite-regular-sequence criterion defining `IsRegularIdealSheaf`. -/
theorem isRegularIdealSheaf_iff
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf)) :
    IsRegularIdealSheaf I ↔
      ∀ x ∈ idealQuotientSupport I,
        ∃ (U : Opens X) (_ : x ∈ U) (r : ℕ) (f : Fin r → (I : X.Modules).val.obj (op U)),
          SectionSequence.IsRegular (fun j ↦ idealSectionToRingSection I U (f j)) ∧
            IsGeneratedByIdealSectionFamilyOn I U f :=
  ⟨fun h ↦ h.locallyGeneratedByRegularSequence, fun h ↦ ⟨h⟩⟩

/-- An ideal sheaf `𝓘 ⊆ 𝒪_X` is Koszul-regular when near every point
of `Supp (𝒪_X / 𝓘)` it is generated by a finite Koszul-regular sequence. -/
@[stacks 063D]
class IsKoszulRegularIdealSheaf
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf)) : Prop where
  /-- Near the quotient support, the ideal sheaf is generated by finite Koszul-regular
  sequences. -/
  locallyGeneratedByKoszulRegularSequence :
    isLocallyGeneratedBySequencePredicate I
      (fun {_ _} f ↦ SectionSequence.IsKoszulRegular f)

/-- The local finite-Koszul-regular-sequence criterion defining `IsKoszulRegularIdealSheaf`. -/
theorem isKoszulRegularIdealSheaf_iff
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf)) :
    IsKoszulRegularIdealSheaf I ↔
      ∀ x ∈ idealQuotientSupport I,
        ∃ (U : Opens X) (_ : x ∈ U) (r : ℕ) (f : Fin r → (I : X.Modules).val.obj (op U)),
          SectionSequence.IsKoszulRegular (fun j ↦ idealSectionToRingSection I U (f j)) ∧
            IsGeneratedByIdealSectionFamilyOn I U f :=
  ⟨fun h ↦ h.locallyGeneratedByKoszulRegularSequence, fun h ↦ ⟨h⟩⟩

/-- An ideal sheaf `𝓘 ⊆ 𝒪_X` is `H_1`-regular when near every point
of `Supp (𝒪_X / 𝓘)` it is generated by a finite `H_1`-regular sequence. -/
@[stacks 063D]
class IsH1RegularIdealSheaf
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf)) : Prop where
  /-- Near the quotient support, the ideal sheaf is generated by finite `H_1`-regular
  sequences. -/
  locallyGeneratedByH1RegularSequence :
    isLocallyGeneratedBySequencePredicate I
      (fun {_ _} f ↦ SectionSequence.IsH1Regular f)

/-- The local finite-`H_1`-regular-sequence criterion defining `IsH1RegularIdealSheaf`. -/
theorem isH1RegularIdealSheaf_iff
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf)) :
    IsH1RegularIdealSheaf I ↔
      ∀ x ∈ idealQuotientSupport I,
        ∃ (U : Opens X) (_ : x ∈ U) (r : ℕ) (f : Fin r → (I : X.Modules).val.obj (op U)),
          SectionSequence.IsH1Regular (fun j ↦ idealSectionToRingSection I U (f j)) ∧
            IsGeneratedByIdealSectionFamilyOn I U f :=
  ⟨fun h ↦ h.locallyGeneratedByH1RegularSequence, fun h ↦ ⟨h⟩⟩

/-- An ideal sheaf `𝓘 ⊆ 𝒪_X` is quasi-regular when near every point
of `Supp (𝒪_X / 𝓘)` it is generated by a finite quasi-regular sequence. -/
@[stacks 063D]
class IsQuasiRegularIdealSheaf
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf)) : Prop where
  /-- Near the quotient support, the ideal sheaf is generated by finite quasi-regular
  sequences. -/
  locallyGeneratedByQuasiRegularSequence :
    isLocallyGeneratedBySequencePredicate I
      (fun {_ _} f ↦ SectionSequence.IsQuasiRegular f)

/-- The local associated-graded quasi-regularity criterion defining
`IsQuasiRegularIdealSheaf`. -/
theorem isQuasiRegularIdealSheaf_iff
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf)) :
    IsQuasiRegularIdealSheaf I ↔
      ∀ x ∈ idealQuotientSupport I,
        ∃ (U : Opens X) (_ : x ∈ U) (r : ℕ) (f : Fin r → (I : X.Modules).val.obj (op U)),
          SectionSequence.IsQuasiRegular (fun j ↦ idealSectionToRingSection I U (f j)) ∧
            IsGeneratedByIdealSectionFamilyOn I U f :=
  ⟨fun h ↦ h.locallyGeneratedByQuasiRegularSequence, fun h ↦ ⟨h⟩⟩

end AlgebraicGeometry.RingedSpace
