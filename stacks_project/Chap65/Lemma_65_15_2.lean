/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import ReasLib.CategoryTheory.Sites.FullyFaithful
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_15_1_InverseImage

/-!
# Lemma 65.15.2

Inverse image along an enlargement of big sites is fully faithful on algebraic
spaces, and the essential image is characterized by sheaf-surjective maps from
objects of the smaller site.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits
open Functor.relativelyRepresentable MorphismProperty

noncomputable section

universe u uC

namespace AlgebraicGeometry.AlgebraicSpace

variable {C : Type uC} [Category.{u} C] (ι : C ⥤ Scheme.{u})
variable (J : GrothendieckTopology C) (X : C)

section InverseImageFullyFaithful

variable [ι.Full] [ι.Faithful] [J.Subcanonical]
variable [(slicePost ι X).IsContinuous (J.over X) (Scheme.fppfTopology.over (ι.obj X))]
variable [(slicePost ι X).IsCocontinuous (J.over X) (Scheme.fppfTopology.over (ι.obj X))]
variable [HasWeakSheafify (J.over X) (Type u)]
variable [HasWeakSheafify (Scheme.fppfTopology.over (ι.obj X)) (Type u)]
variable [∀ P : (Over X)ᵒᵖ ⥤ Type u, (slicePost ι X).op.HasLeftKanExtension P]
variable [∀ P : (Over X)ᵒᵖ ⥤ Type u, (slicePost ι X).op.HasPointwiseLeftKanExtension P]
variable [∀ P : (Over X)ᵒᵖ ⥤ Type u, (slicePost ι X).op.HasPointwiseRightKanExtension P]
variable [PreservesFiniteLimits
    ((slicePost ι X).sheafPullback (Type u) (J.over X)
      (Scheme.fppfTopology.over (ι.obj X)))]

/-- Lemma 65.15.2 (1): suppose `Sch_fppf` is contained in `Sch'_fppf`, and let `S` be an
object of `Sch_fppf`. Write `Spaces/S` for algebraic spaces over `S` defined using
`Sch_fppf`, and `Spaces'/S` for those defined using `Sch'_fppf`. The inverse-image
construction of Lemma 65.15.1 is bijective on morphisms of sheaves, and therefore
induces a fully faithful functor `Spaces/S ⟶ Spaces'/S`. -/
@[stacks 04W1]
theorem inverseImage_map_bijective (F G : Sheaf (J.over X) (Type u)) :
    Function.Bijective
      (fun f : F ⟶ G ↦ (inverseImage ι X J Scheme.fppfTopology).map f) := sorry

/-- Inverse image of sheaves along a fully faithful continuous and cocontinuous
enlargement of big sites is a full functor. -/
instance inverseImage_full : (inverseImage ι X J Scheme.fppfTopology).Full := sorry

/-- Inverse image of sheaves along a fully faithful continuous and cocontinuous
enlargement of big sites is a faithful functor. -/
instance inverseImage_faithful :
    (inverseImage ι X J Scheme.fppfTopology).Faithful := sorry

end InverseImageFullyFaithful

section EssentialImage

variable [HasPullbacks ((Over (ι.obj X))ᵒᵖ ⥤ Type u)]

/-- An algebraic space `X'` on the larger slice admits objects `U`, `R` of the smaller
slice together with sheaf-surjective maps `U ⟶ X'` and `R ⟶ U ×_{X'} U`. -/
def HasSmallSiteSurjections (X' : AlgebraicSpace (ι.obj X)) : Prop :=
  ∃ (U R : Over X)
      (π : yoneda.obj ((slicePost ι X).obj U) ⟶ X'.functorOfPoints)
      (σ : yoneda.obj ((slicePost ι X).obj R) ⟶ pullback π π),
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (ι.obj X)) π ∧
      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (ι.obj X)) σ

/-- Representable étale and surjective maps from objects of the smaller slice are
surjective as maps of sheaves, and therefore witness `HasSmallSiteSurjections`. -/
theorem hasSmallSiteSurjections_of_etaleSurjective
    {X' : AlgebraicSpace (ι.obj X)} {U R : Over X}
    (π : yoneda.obj ((slicePost ι X).obj U) ⟶ X'.functorOfPoints)
    (σ : yoneda.obj ((slicePost ι X).obj R) ⟶ pullback π π)
    (hπ : (over (@Etale ⊓ @Surjective)).presheaf π)
    (hσ : (over (@Etale ⊓ @Surjective)).presheaf σ) :
    HasSmallSiteSurjections ι X X' := sorry

variable [ι.Full] [ι.Faithful] [J.Subcanonical]
variable [PreservesLimitsOfShape WalkingCospan ι]
variable [(slicePost ι X).IsContinuous (J.over X) (Scheme.fppfTopology.over (ι.obj X))]
variable [HasWeakSheafify (Scheme.fppfTopology.over (ι.obj X)) (Type u)]
variable [∀ P : (Over X)ᵒᵖ ⥤ Type u, (slicePost ι X).op.HasLeftKanExtension P]
variable [PreservesFiniteLimits
    ((slicePost ι X).sheafPullback (Type u) (J.over X)
      (Scheme.fppfTopology.over (ι.obj X)))]

/-- Lemma 65.15.2 (2): in the same setup, the essential image of `Spaces/S ⟶ Spaces'/S`
consists of those `X'` in `Spaces'/S` for which there exist `U`, `R` in `(Sch/S)_fppf`
and morphisms `U ⟶ X'` and `R ⟶ U ×_{X'} U` in `Sh((Sch'/S)_fppf)` that are surjective
as maps of sheaves. -/
@[stacks 04W1]
theorem iso_ofInverseImage_iff (X' : AlgebraicSpace (ι.obj X)) :
    (∃ (F : Sheaf (J.over X) (Type u))
        (hdiag : yoneda.relativelyRepresentable (Limits.diag F.obj))
        (U₀ : Over X) (p : yoneda.obj U₀ ⟶ F.obj)
        (hp : yoneda.relativelyRepresentable p)
        (hp_etale : ∀ {V : Over X} (ξ : yoneda.obj V ⟶ F.obj),
          (over (@Etale)) ((slicePost ι X).map (hp.snd ξ)))
        (hp_surj : ∀ {V : Over X} (ξ : yoneda.obj V ⟶ F.obj),
          Surjective ((slicePost ι X).map (hp.snd ξ)).left),
      Nonempty (ofInverseImage ι J X F hdiag p hp hp_etale hp_surj ≅ X')) ↔
      HasSmallSiteSurjections ι X X' := sorry

end EssentialImage

end AlgebraicGeometry.AlgebraicSpace
