module

public import Mathlib.CategoryTheory.Limits.Presheaf
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

/-- Explicit inverse image of `f_small` as restriction after pullback along `etaleBaseChange`. -/
def etaleRelocalizeExplicitInverseImage {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Sheaf (smallEtaleTopology Y) (Type u) ⥤ Sheaf (smallEtaleTopology X) (Type u) :=
  Functor.sheafPullbackConstruction.sheafPullback (etaleBaseChange f) (Type u)
      (smallEtaleTopology Y) (spacesEtaleTopology X) ⋙
    etaleInclusionRestriction X

/-- The explicit inverse image is left adjoint to `typePushforward`. -/
def etaleRelocalizeExplicitInverseImage_adjunction {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    etaleRelocalizeExplicitInverseImage f ⊣ typePushforward f :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (etaleBaseChange f) (Type u)
      (smallEtaleTopology Y) (spacesEtaleTopology X)).comp
    ((smallEtaleInclusion X).sheafAdjunctionCocontinuous (Type u)
      (smallEtaleTopology X) (spacesEtaleTopology X))

/-- Comparison of the explicit inverse image with the chosen left adjoint of `typePushforward`. -/
def etaleRelocalizeInverseImageIso {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    etaleRelocalizeExplicitInverseImage f ≅ (morphismOfTopoi f).inverseImage :=
  Adjunction.leftAdjointUniq
    (etaleRelocalizeExplicitInverseImage_adjunction f) (morphismOfTopoi f).adjunction

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

/-- The Yoneda image of the spaces-étale arrow corresponding to `g`, as a map of Type-`u`
presheaves obtained from the unit of left Kan extension along `etaleBaseChange`. -/
def etaleRelocalizeParameterLanSection (hcomm : p ≫ f = g ≫ q) :
    ((etaleBaseChange f).op.lan.obj (yoneda.obj (smallEtaleSite.mk q))).obj
      (op ((smallEtaleInclusion X).obj (smallEtaleSite.mk p))) :=
  ((etaleBaseChange f).op.lan.obj (yoneda.obj (smallEtaleSite.mk q))).map
      (etaleRelocalizeParameterArrow p g f q hcomm).op
    (((etaleBaseChange f).op.lanUnit.app (yoneda.obj (smallEtaleSite.mk q))).app
      (op (smallEtaleSite.mk q)) (𝟙 _))

/-- The Lan section of `c`, sheafified as a section of the constructed pullback of `h_V`. -/
def etaleRelocalizeParameterPullbackSection (hcomm : p ≫ f = g ≫ q) :
    ((Functor.sheafPullbackConstruction.sheafPullback (etaleBaseChange f) (Type u)
          (smallEtaleTopology Y) (spacesEtaleTopology X)).obj
        (etaleRepresentable (smallEtaleSite.mk q))).obj.obj
      (op ((smallEtaleInclusion X).obj (smallEtaleSite.mk p))) :=
  ((sheafificationAdjunction (spacesEtaleTopology X) (Type u)).unit.app
      ((etaleBaseChange f).op.lan.obj (yoneda.obj (smallEtaleSite.mk q)))).app
    (op ((smallEtaleInclusion X).obj (smallEtaleSite.mk p)))
    (etaleRelocalizeParameterLanSection p g f q hcomm)

/-- The section of `f_small⁻¹ h_V` over `U` corresponding to `g`. -/
def etaleRelocalizeParameterSection (hcomm : p ≫ f = g ≫ q) :
    ((etaleRelocalizeExplicitInverseImage f).obj
        (etaleRepresentable (smallEtaleSite.mk q))).obj.obj
      (op (smallEtaleSite.mk p)) :=
  (Functor.sheafPushforwardContinuousObjObjIso (smallEtaleInclusion X) (Type u)
      ((Functor.sheafPullbackConstruction.sheafPullback (etaleBaseChange f) (Type u)
          (smallEtaleTopology Y) (spacesEtaleTopology X)).obj
        (etaleRepresentable (smallEtaleSite.mk q)))
      (smallEtaleSite.mk p)).inv
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
