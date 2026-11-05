/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Adjunction.Unique
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.CommRing
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Restriction
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.SameSiteTensorExtension.Monoidal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal.Ringed

/-!
# Monoidal comparisons for module-presheaf sheafification

This leaf owns the tensor comparison API induced by an explicitly supplied
monoidal structure on module sheafification.  It is stated for arbitrary ring
presheaves and ring sheaves, so geometric specializations only need thin views.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R₀ : Cᵒᵖ ⥤ RingCat.{max u v}} {R : Sheaf J RingCat.{max u v}}
variable (α : R₀ ⟶ R.obj)
variable [Presheaf.IsLocallyInjective J α]
variable [Presheaf.IsLocallySurjective J α]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [MonoidalCategory (PresheafOfModules R₀)]
variable [MonoidalCategory (SheafOfModules R)]
variable [Functor.Monoidal (sheafification α)]

/-- The tensor comparison from the tensor product of two sheafified module presheaves to the
sheafification of their tensor product. -/
noncomputable abbrev sheafificationTensorIso
    (ℱ 𝒢 : PresheafOfModules R₀) :
    CategoryTheory.MonoidalCategory.tensorObj
        ((sheafification α).obj ℱ)
        ((sheafification α).obj 𝒢) ≅
      (sheafification α).obj
        (CategoryTheory.MonoidalCategory.tensorObj ℱ 𝒢) :=
  Functor.Monoidal.μIso (sheafification α) ℱ 𝒢

/-- The oplax tensor comparison from sheafification of a tensor product to the tensor product of
the two sheafifications. -/
noncomputable abbrev sheafificationTensorComparison
    (ℱ 𝒢 : PresheafOfModules R₀) :
    (sheafification α).obj
        (CategoryTheory.MonoidalCategory.tensorObj ℱ 𝒢) ⟶
      CategoryTheory.MonoidalCategory.tensorObj
        ((sheafification α).obj ℱ)
        ((sheafification α).obj 𝒢) :=
  (sheafificationTensorIso α ℱ 𝒢).inv

/-- Module sheafification commutes with right tensoring through its supplied monoidal
comparison. -/
noncomputable abbrev sheafificationTensorRightIso
    (ℱ : PresheafOfModules R₀) :
    CategoryTheory.MonoidalCategory.tensorRight ℱ ⋙ sheafification α ≅
      sheafification α ⋙
        CategoryTheory.MonoidalCategory.tensorRight ((sheafification α).obj ℱ) :=
  (Functor.Monoidal.commTensorRight (sheafification α) ℱ).symm

/-- Module sheafification commutes with left tensoring through its supplied monoidal
comparison. -/
noncomputable abbrev sheafificationTensorLeftIso
    (ℱ : PresheafOfModules R₀) :
    CategoryTheory.MonoidalCategory.tensorLeft ℱ ⋙ sheafification α ≅
      sheafification α ⋙
        CategoryTheory.MonoidalCategory.tensorLeft ((sheafification α).obj ℱ) :=
  (Functor.Monoidal.commTensorLeft (sheafification α) ℱ).symm

end PresheafOfModules

namespace PresheafOfModules

section CommRing

set_option backward.isDefEq.respectTransparency false

universe w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O : Cᵒᵖ ⥤ CommRingCat.{w}} {S : Sheaf J CommRingCat.{w}}
variable (α : O ⟶ S.obj)

/-- Sectionwise extension of scalars followed by ordinary module sheafification is left
adjoint to forgetting the sheaf condition and restricting scalars along `α`. -/
noncomputable def sheafificationExtensionAdjunction :
    SameSiteTensorExtension.functor α ⋙
        sheafification.{w} (J := J) (R := Sheaf.ringSheafOfComm S) (𝟙 (ringPresheaf S.obj)) ⊣
      SheafOfModules.forget (Sheaf.ringSheafOfComm S) ⋙
        restrictScalars (presheafStructureMap α) :=
  (SameSiteTensorExtension.adjunction α).comp
    ((sheafificationAdjunction.{w} (J := J) (R := Sheaf.ringSheafOfComm S)
      (𝟙 (ringPresheaf S.obj))).ofNatIsoRight
        ((Functor.isoWhiskerLeft (SheafOfModules.forget (Sheaf.ringSheafOfComm S))
          (Restriction.idIso (ringPresheaf S.obj)).symm) ≪≫
            (SheafOfModules.forget (Sheaf.ringSheafOfComm S)).rightUnitor))

variable [Presheaf.IsLocallyInjective J (presheafStructureMap α)]
variable [Presheaf.IsLocallySurjective J (presheafStructureMap α)]

/-- The canonical identification of coefficient extension followed by ordinary sheafification
with sheafification along a locally bijective coefficient map. Both directions come from the
implemented adjunctions, rather than from a chosen existence or invertibility proof. -/
noncomputable def sheafificationExtensionIso :
    SameSiteTensorExtension.functor α ⋙
        sheafification.{w} (J := J) (R := Sheaf.ringSheafOfComm S) (𝟙 (ringPresheaf S.obj)) ≅
      sheafification.{w} (J := J) (R := Sheaf.ringSheafOfComm S) (presheafStructureMap α) :=
  (sheafificationExtensionAdjunction (J := J) α).leftAdjointUniq
    (sheafificationAdjunction.{w} (J := J) (R := Sheaf.ringSheafOfComm S) (presheafStructureMap α))

/-- This identification preserves the sheafification unit, which fixes its normalization. -/
@[reassoc]
theorem sheafificationExtensionIso_unit
    (M : PresheafOfModules.{w} (ringPresheaf O)) :
    (sheafificationExtensionAdjunction (J := J) α).unit.app M ≫
        (SheafOfModules.forget (Sheaf.ringSheafOfComm S) ⋙
          restrictScalars (presheafStructureMap α)).map
            ((sheafificationExtensionIso (J := J) α).hom.app M) =
      (sheafificationAdjunction.{w} (J := J) (R := Sheaf.ringSheafOfComm S) (presheafStructureMap α)).unit.app M :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ M

/-- The canonical strong monoidal structure on sheafification along a locally bijective map
of commutative-ring presheaves. Its tensor maps are transported from sectionwise scalar
extension and fixed-ring sheafification through the unit-preserving comparison above.
This is explicit data, so callers need not supply an arbitrary monoidal structure. -/
@[implicit_reducible]
noncomputable def sheafificationMonoidalOfComm :
    (sheafification.{w} (J := J) (R := Sheaf.ringSheafOfComm S) (presheafStructureMap α)).Monoidal := by
  letI : (SameSiteTensorExtension.functor α).Monoidal :=
    (SameSiteTensorExtension.coreMonoidal α).toMonoidal
  letI : (sheafification.{w} (J := J) (R := Sheaf.ringSheafOfComm S)
      (𝟙 (ringPresheaf S.obj))).Monoidal :=
    SheafOfModules.RingedSite.Tensor.sheafificationMonoidal (J := J) S
  exact Functor.Monoidal.transport (sheafificationExtensionIso (J := J) α)

/-- The tensor comparison is the scalar-extension/ordinary-sheafification comparison
conjugated by the unit-preserving identification. In particular its normalization is fixed
by the sectionwise base-change maps, rather than an arbitrary monoidal structure. -/
theorem sheafificationMonoidalOfComm_μ
    (M N : PresheafOfModules.{w} (ringPresheaf O)) :
    letI : (SameSiteTensorExtension.functor α).Monoidal :=
    (SameSiteTensorExtension.coreMonoidal α).toMonoidal
    letI : (sheafification.{w} (J := J) (R := Sheaf.ringSheafOfComm S)
      (𝟙 (ringPresheaf S.obj))).Monoidal :=
    SheafOfModules.RingedSite.Tensor.sheafificationMonoidal (J := J) S
    letI := sheafificationMonoidalOfComm (J := J) α
    Functor.LaxMonoidal.μ
        (sheafification.{w} (J := J) (R := Sheaf.ringSheafOfComm S)
          (presheafStructureMap α)) M N =
      ((sheafificationExtensionIso (J := J) α).inv.app M ⊗ₘ
          (sheafificationExtensionIso (J := J) α).inv.app N) ≫
        Functor.LaxMonoidal.μ
          (SameSiteTensorExtension.functor α ⋙
            sheafification.{w} (J := J) (R := Sheaf.ringSheafOfComm S)
              (𝟙 (ringPresheaf S.obj))) M N ≫
        (sheafificationExtensionIso (J := J) α).hom.app (M ⊗ N) := by
  rfl

end CommRing

end PresheafOfModules
