/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SchemeLocalization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SheafAdjunction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.PullbackLift
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.SpacesHom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage

public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.ShrinkYoneda
public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Subcanonical


public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite
open CategoryTheory.GrothendieckTopology

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The small étale topology of an algebraic space is subcanonical. -/
instance smallEtaleTopology.instSubcanonical (X : AlgebraicSpace S) :
    (smallEtaleTopology X).Subcanonical :=
  sorry

/-- The representable sheaf `h_U` on the small étale site of `X`. -/
abbrev etaleRepresentable {X : AlgebraicSpace S} (U : smallEtaleSite X) :
    Sheaf (smallEtaleTopology X) (Type u) :=
  (smallEtaleTopology X).yoneda.obj U

/-- The identity map of a scheme respects its chart inclusion structure map. -/
private theorem smallEtaleInclusion_mkIso_w {X : AlgebraicSpace S} {U : Over S}
    (φ : ofOver U ⟶ X) [Etale φ] :
    (𝟙 (ofOver U)) ≫ (spacesEtaleSite.mk φ).hom =
      ((smallEtaleToSpaces X).obj (smallEtaleSite.mk φ)).hom := sorry

/-- Identifying a scheme étale over `X` with the same object of `X_spaces,étale`. -/
@[expose]
def smallEtaleInclusion_mkIso {X : AlgebraicSpace S} {U : Over S} (φ : ofOver U ⟶ X)
    [Etale φ] :
    (smallEtaleToSpaces X).obj (smallEtaleSite.mk φ) ≅ spacesEtaleSite.mk φ :=
  MorphismProperty.Over.isoMk (Iso.refl _) (by exact smallEtaleInclusion_mkIso_w φ)

/-- The underlying algebraic-space morphism of `smallEtaleInclusion_mkIso` is the identity. -/
@[simp]
theorem smallEtaleInclusion_mkIso_hom_left {X : AlgebraicSpace S} {U : Over S}
    (φ : ofOver U ⟶ X) [Etale φ] :
    (smallEtaleInclusion_mkIso φ).hom.left = 𝟙 (ofOver U) :=
  rfl


/-- Comparison of the explicit inverse image with the chosen left adjoint of `typePushforward`. -/
@[expose]
def etaleRelocalizeInverseImageIso {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    EtaleTopos.inverseImage f ≅ (morphismOfTopoi f).inverseImage :=
  Adjunction.leftAdjointUniq
    (EtaleTopos.adjunction f) (morphismOfTopoi f).adjunction

/-- The small-Hom representable presheaf on the spaces étale site is a sheaf. -/
private theorem spacesEtaleRepresentable_isSheaf {X : AlgebraicSpace S}
    (W : spacesEtaleSite X) : Presheaf.IsSheaf (spacesEtaleTopology X)
      (shrinkYoneda.{u}.obj W) := sorry

/-- A spaces-étale object represents its actual small Hom sets, without changing morphisms. -/
@[expose]
def spacesEtaleRepresentable {X : AlgebraicSpace S} (W : spacesEtaleSite X) :
    Sheaf (spacesEtaleTopology X) (Type u) :=
  ⟨shrinkYoneda.{u}.obj W, by exact spacesEtaleRepresentable_isSheaf W⟩

/-- Yoneda evaluation for the concrete small-Hom representable sheaf. -/
@[expose]
def spacesEtaleRepresentableHomEquiv {X : AlgebraicSpace S} (W : spacesEtaleSite X)
    (N : Sheaf (spacesEtaleTopology X) (Type u)) :
    (spacesEtaleRepresentable W ⟶ N) ≃ N.obj.obj (op W) :=
  (fullyFaithfulSheafToPresheaf _ _).homEquiv.trans shrinkYonedaEquiv

/-- The restricted geometric fibre product represents inverse image of a scheme representable. -/
@[expose]
def etaleRepresentablePullback {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (V : smallEtaleSite Y) : Sheaf (smallEtaleTopology X) (Type u) :=
  (EtaleTopos.restriction X).obj (spacesEtaleRepresentable ((etaleBaseChange f).obj V))

/-- The actual dense-site adjunction and Yoneda evaluation identify the represented Hom functor. -/
@[expose]
def etaleRepresentablePullbackHomEquiv {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (V : smallEtaleSite Y) (N : Sheaf (smallEtaleTopology X) (Type u)) :
    (etaleRepresentablePullback f V ⟶ N) ≃ ((typePushforward f).obj N).obj.obj (op V) :=
  ((EtaleTopos.siteEquivalence X).toAdjunction.homEquiv _ _).trans
    (spacesEtaleRepresentableHomEquiv ((etaleBaseChange f).obj V) ((EtaleTopos.extension X).obj N))

/-- Adjunction and Yoneda evaluation give the same Hom functor for the specified inverse image. -/
@[expose]
def etaleInverseRepresentableHomEquiv {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (V : smallEtaleSite Y) (N : Sheaf (smallEtaleTopology X) (Type u)) :
    ((EtaleTopos.inverseImage f).obj (etaleRepresentable V) ⟶ N) ≃
      ((typePushforward f).obj N).obj.obj (op V) :=
  ((EtaleTopos.adjunction f).homEquiv _ _).trans
    (smallEtaleTopology Y).yonedaEquiv

/-- The two universal-property transposes compose to the identity on inverse image. -/
private theorem etaleRepresentablePullbackIso_hom_inv_id {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (V : smallEtaleSite Y) :
    (etaleInverseRepresentableHomEquiv f V _).symm
        (etaleRepresentablePullbackHomEquiv f V _ (𝟙 _)) ≫
      (etaleRepresentablePullbackHomEquiv f V _).symm
        (etaleInverseRepresentableHomEquiv f V _ (𝟙 _)) =
      𝟙 ((EtaleTopos.inverseImage f).obj (etaleRepresentable V)) := sorry

/-- The two universal-property transposes compose to the identity on the pullback representable. -/
private theorem etaleRepresentablePullbackIso_inv_hom_id {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (V : smallEtaleSite Y) :
    (etaleRepresentablePullbackHomEquiv f V _).symm
        (etaleInverseRepresentableHomEquiv f V _ (𝟙 _)) ≫
      (etaleInverseRepresentableHomEquiv f V _).symm
        (etaleRepresentablePullbackHomEquiv f V _ (𝟙 _)) =
      𝟙 (etaleRepresentablePullback f V) := sorry

/-- Both comparison maps are universal-property transposes of identity maps. -/
@[expose]
def etaleRepresentablePullbackIso {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (V : smallEtaleSite Y) :
    (EtaleTopos.inverseImage f).obj (etaleRepresentable V) ≅
      etaleRepresentablePullback f V where
  hom := (etaleInverseRepresentableHomEquiv f V _).symm
    (etaleRepresentablePullbackHomEquiv f V _ (𝟙 _))
  inv := (etaleRepresentablePullbackHomEquiv f V _).symm
    (etaleInverseRepresentableHomEquiv f V _ (𝟙 _))
  hom_inv_id := by exact etaleRepresentablePullbackIso_hom_inv_id f V
  inv_hom_id := by exact etaleRepresentablePullbackIso_inv_hom_id f V

variable {U V : Over S} {X Y : AlgebraicSpace S}
variable (p : ofOver U ⟶ X) (g : ofOver U ⟶ ofOver V) (f : X ⟶ Y) (q : ofOver V ⟶ Y)
variable [Etale p] [Etale q]

/-- The spaces-étale arrow `c` corresponding to `g`, as a map into the étale base change of `V`. -/
@[expose]
def etaleRelocalizeParameterArrow (hcomm : p ≫ f = g ≫ q) :
    (smallEtaleToSpaces X).obj (smallEtaleSite.mk p) ⟶
      (etaleBaseChange f).obj (smallEtaleSite.mk q) :=
  (smallEtaleInclusion_mkIso p).hom ≫
    spacesEtalePullbackLift p g f q hcomm ≫
      (spacesEtalePullback f).map (smallEtaleInclusion_mkIso q).inv ≫
        (smallEtaleInclusion_comp_spacesEtalePullback f).hom.app (smallEtaleSite.mk q)

/-- The Yoneda section of the actual fibre-product arrow, represented in the original universe. -/
private def etaleRelocalizeParameterLanSection (hcomm : p ≫ f = g ≫ q) :
    (spacesEtaleRepresentable ((etaleBaseChange f).obj (smallEtaleSite.mk q))).obj.obj
      (op ((smallEtaleToSpaces X).obj (smallEtaleSite.mk p))) :=
  shrinkYonedaObjObjEquiv.symm (etaleRelocalizeParameterArrow p g f q hcomm)

/-- The geometric section on the restricted representable fibre product. -/
private def etaleRelocalizeParameterPullbackSection (hcomm : p ≫ f = g ≫ q) :
    (etaleRepresentablePullback f (smallEtaleSite.mk q)).obj.obj (op (smallEtaleSite.mk p)) :=
  etaleRelocalizeParameterLanSection p g f q hcomm

/-- The section of `f_small⁻¹ h_V` over `U` corresponding to `g`. -/
def etaleRelocalizeParameterSection (hcomm : p ≫ f = g ≫ q) :
    ((EtaleTopos.inverseImage f).obj
        (etaleRepresentable (smallEtaleSite.mk q))).obj.obj
      (op (smallEtaleSite.mk p)) :=
  by
    exact ((etaleRepresentablePullbackIso f (smallEtaleSite.mk q)).inv.hom.app
      (op (smallEtaleSite.mk p))) (etaleRelocalizeParameterPullbackSection p g f q hcomm)

/-- The map `s : h_U ⟶ f_small⁻¹ h_V` corresponding to `g`. -/
@[expose]
def etaleRelocalizeParameter (hcomm : p ≫ f = g ≫ q) :
    etaleRepresentable (smallEtaleSite.mk p) ⟶
      (morphismOfTopoi f).inverseImage.obj (etaleRepresentable (smallEtaleSite.mk q)) :=
  (smallEtaleTopology X).yonedaEquiv.symm
      (etaleRelocalizeParameterSection p g f q hcomm) ≫
    (etaleRelocalizeInverseImageIso f).hom.app (etaleRepresentable (smallEtaleSite.mk q))

/-- The parameter `s` is the Yoneda transpose of the section of `f_small⁻¹ h_V` over `U`
determined by the spaces-étale arrow `c`. -/
theorem etaleRelocalizeParameter_spec (hcomm : p ≫ f = g ≫ q) :
    (smallEtaleTopology X).yonedaEquiv
        ((etaleRelocalizeParameter p g f q hcomm) ≫
          (etaleRelocalizeInverseImageIso f).inv.app
            (etaleRepresentable (smallEtaleSite.mk q))) =
      etaleRelocalizeParameterSection p g f q hcomm :=
  by simp [etaleRelocalizeParameter]

end AlgebraicGeometry.AlgebraicSpace
