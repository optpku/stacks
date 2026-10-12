/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.ShrinkYoneda
public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import stacks_project.Chap66.Lemma_66_18_3
public import stacks_project.Chap66.Lemma_66_20_1_Sheaf
public import stacks_project.Chap66.Lemma_66_27_1_BaseChange
public import stacks_project.Chap66.Lemma_66_27_1_Hom
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap66.«66_18_11_1_Restrict»
public import stacks_project.Chap66.«66_27_0_4_Comparison»

/-!
# Representable parameter for small-étale relocalization

A commutative square with scheme-étale vertical arrows determines the sheaf map
`s : h_U ⟶ f_small⁻¹ h_V` corresponding to `g` as the adjunct of the Yoneda image of the
spaces-étale arrow `c`.
-/

@[expose] public section

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

/-- Identifying a scheme étale over `X` with the same object of `X_spaces,étale`. -/
def smallEtaleInclusion_mkIso {X : AlgebraicSpace S} {U : Over S} (φ : ofOver U ⟶ X)
    [Etale φ] :
    (smallEtaleInclusion X).obj (smallEtaleSite.mk φ) ≅ spacesEtaleSite.mk φ :=
  MorphismProperty.Over.isoMk (Iso.refl _) sorry

/-- The underlying algebraic-space morphism of `smallEtaleInclusion_mkIso` is the identity. -/
@[simp]
theorem smallEtaleInclusion_mkIso_hom_left {X : AlgebraicSpace S} {U : Over S}
    (φ : ofOver U ⟶ X) [Etale φ] :
    (smallEtaleInclusion_mkIso φ).hom.left = 𝟙 (ofOver U) :=
  rfl

/-- Restriction of a type-valued spaces-étale sheaf along `smallEtaleInclusion X`. -/
def etaleInclusionRestriction (X : AlgebraicSpace S) :
    Sheaf (spacesEtaleTopology X) (Type u) ⥤ Sheaf (smallEtaleTopology X) (Type u) :=
  (smallEtaleInclusion X).sheafPushforwardContinuous (Type u)
    (smallEtaleTopology X) (spacesEtaleTopology X)

/-- Weak sheafification of type-valued sheaves exists on the spaces-étale topology. -/
instance spacesEtaleTopology_hasWeakSheafify_type (X : AlgebraicSpace S) :
    HasWeakSheafify (spacesEtaleTopology X) (Type u) :=
  sorry

/-- The opposite of `etaleBaseChange f` has left Kan extensions on type-valued presheaves. -/
instance etaleBaseChange_op_hasLeftKanExtension {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (P : (smallEtaleSite Y)ᵒᵖ ⥤ Type u) :
    (etaleBaseChange f).op.HasLeftKanExtension P :=
  sorry

/-- Inverse image uses the explicit small-chart Kan construction and sheafification. -/
def etaleRelocalizeExplicitInverseImage {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Sheaf (smallEtaleTopology Y) (Type u) ⥤ Sheaf (smallEtaleTopology X) (Type u) :=
  EtaleTopos.inverseImage f

/-- The explicit inverse image is left adjoint to `typePushforward`. -/
def etaleRelocalizeExplicitInverseImage_adjunction {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    etaleRelocalizeExplicitInverseImage f ⊣ typePushforward f :=
  EtaleTopos.adjunction f

/-- Comparison of the explicit inverse image with the chosen left adjoint of `typePushforward`. -/
def etaleRelocalizeInverseImageIso {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    etaleRelocalizeExplicitInverseImage f ≅ (morphismOfTopoi f).inverseImage :=
  Adjunction.leftAdjointUniq
    (etaleRelocalizeExplicitInverseImage_adjunction f) (morphismOfTopoi f).adjunction

/-- A spaces-étale object represents its actual small Hom sets, without changing morphisms. -/
def spacesEtaleRepresentable {X : AlgebraicSpace S} (W : spacesEtaleSite X) :
    Sheaf (spacesEtaleTopology X) (Type u) :=
  ⟨shrinkYoneda.{u}.obj W, by sorry⟩

/-- Yoneda evaluation for the concrete small-Hom representable sheaf. -/
def spacesEtaleRepresentableHomEquiv {X : AlgebraicSpace S} (W : spacesEtaleSite X)
    (N : Sheaf (spacesEtaleTopology X) (Type u)) :
    (spacesEtaleRepresentable W ⟶ N) ≃ N.obj.obj (op W) :=
  (fullyFaithfulSheafToPresheaf _ _).homEquiv.trans shrinkYonedaEquiv

/-- The restricted geometric fibre product represents inverse image of a scheme representable. -/
def etaleRepresentablePullback {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (V : smallEtaleSite Y) : Sheaf (smallEtaleTopology X) (Type u) :=
  (EtaleTopos.restriction X).obj (spacesEtaleRepresentable ((etaleBaseChange f).obj V))

/-- The actual dense-site adjunction and Yoneda evaluation identify the represented Hom functor. -/
def etaleRepresentablePullbackHomEquiv {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (V : smallEtaleSite Y) (N : Sheaf (smallEtaleTopology X) (Type u)) :
    (etaleRepresentablePullback f V ⟶ N) ≃ ((typePushforward f).obj N).obj.obj (op V) :=
  ((EtaleTopos.siteEquivalence X).toAdjunction.homEquiv _ _).trans
    (spacesEtaleRepresentableHomEquiv ((etaleBaseChange f).obj V) ((EtaleTopos.extension X).obj N))

/-- Adjunction and Yoneda evaluation give the same Hom functor for the specified inverse image. -/
def etaleInverseRepresentableHomEquiv {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (V : smallEtaleSite Y) (N : Sheaf (smallEtaleTopology X) (Type u)) :
    ((etaleRelocalizeExplicitInverseImage f).obj (etaleRepresentable V) ⟶ N) ≃
      ((typePushforward f).obj N).obj.obj (op V) :=
  ((etaleRelocalizeExplicitInverseImage_adjunction f).homEquiv _ _).trans
    (smallEtaleTopology Y).yonedaEquiv

/-- Both comparison maps are universal-property transposes of identity maps. -/
def etaleRepresentablePullbackIso {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (V : smallEtaleSite Y) :
    (etaleRelocalizeExplicitInverseImage f).obj (etaleRepresentable V) ≅
      etaleRepresentablePullback f V where
  hom := (etaleInverseRepresentableHomEquiv f V _).symm
    (etaleRepresentablePullbackHomEquiv f V _ (𝟙 _))
  inv := (etaleRepresentablePullbackHomEquiv f V _).symm
    (etaleInverseRepresentableHomEquiv f V _ (𝟙 _))
  hom_inv_id := sorry
  inv_hom_id := sorry

variable {U V : Over S} {X Y : AlgebraicSpace S}
variable (p : ofOver U ⟶ X) (g : ofOver U ⟶ ofOver V) (f : X ⟶ Y) (q : ofOver V ⟶ Y)
variable [Etale p] [Etale q]

/-- The spaces-étale arrow `c` corresponding to `g`, as a map into the étale base change of `V`. -/
def etaleRelocalizeParameterArrow (hcomm : p ≫ f = g ≫ q) :
    (smallEtaleInclusion X).obj (smallEtaleSite.mk p) ⟶
      (etaleBaseChange f).obj (smallEtaleSite.mk q) :=
  (smallEtaleInclusion_mkIso p).hom ≫
    spacesEtalePullbackLift p g f q hcomm ≫
      (spacesEtalePullback f).map (smallEtaleInclusion_mkIso q).inv ≫
        (smallEtaleInclusion_comp_spacesEtalePullback f).hom.app (smallEtaleSite.mk q)

/-- The Yoneda section of the actual fibre-product arrow, represented in the original universe. -/
def etaleRelocalizeParameterLanSection (hcomm : p ≫ f = g ≫ q) :
    (spacesEtaleRepresentable ((etaleBaseChange f).obj (smallEtaleSite.mk q))).obj.obj
      (op ((smallEtaleInclusion X).obj (smallEtaleSite.mk p))) :=
  shrinkYonedaObjObjEquiv.symm (etaleRelocalizeParameterArrow p g f q hcomm)

/-- The geometric section on the restricted representable fibre product. -/
def etaleRelocalizeParameterPullbackSection (hcomm : p ≫ f = g ≫ q) :
    (etaleRepresentablePullback f (smallEtaleSite.mk q)).obj.obj (op (smallEtaleSite.mk p)) :=
  etaleRelocalizeParameterLanSection p g f q hcomm

/-- The section of `f_small⁻¹ h_V` over `U` corresponding to `g`. -/
def etaleRelocalizeParameterSection (hcomm : p ≫ f = g ≫ q) :
    ((etaleRelocalizeExplicitInverseImage f).obj
        (etaleRepresentable (smallEtaleSite.mk q))).obj.obj
      (op (smallEtaleSite.mk p)) :=
  ((etaleRepresentablePullbackIso f (smallEtaleSite.mk q)).inv.hom.app (op (smallEtaleSite.mk p)))
    (etaleRelocalizeParameterPullbackSection p g f q hcomm)

/-- The map `s : h_U ⟶ f_small⁻¹ h_V` corresponding to `g`. -/
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
