/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Localization.Construction
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Definition
public import ReasLib.CategoryTheory.Fibered.CoGrothendieck.Presheaf
public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Existence
public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Stackification
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification.Existence
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap78.Lemma_78_28_1_InverseImage
public import stacks_project.Chap78.Lemma_78_28_1_Quotient

/-!
# Change-of-big-site comparison for quotient stacks

The proof of Lemma 78.28.1 constructs an explicit cartesian functor
`u_p[U/_p R] ⟶ [f⁻¹U/_p f⁻¹R]` by `(T', φ, x) ↦ x ∘ φ`. Stackifying that functor
against the 04WR comparison `u_p[U/_p R] ⟶ f⁻¹[U/R]` yields a morphism
`f⁻¹[U/R] ⟶ [f⁻¹U/f⁻¹R]` of stacks in groupoids over `(Sch'/S)_fppf`. The book
arrow `[f⁻¹U/f⁻¹R] ⟶ f⁻¹[U/R]` is the quasi-inverse of this displayed morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupoidAlgebraicSpace CategoryTheory.Limits Opposite
open Functor.IsFibered.InGroupoids.Stackification
open CategoryTheory.Pseudofunctor.CoGrothendieck

noncomputable section

universe u uC w

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

variable {C : Type uC} [Category.{u} C] (ι : C ⥤ Scheme.{u})
variable (J : GrothendieckTopology C) (S : C)
variable [ι.Full] [ι.Faithful] [J.Subcanonical]
variable [PreservesLimitsOfShape WalkingCospan ι]
variable [(slicePost ι S).IsContinuous (J.over S) (Scheme.fppfTopology.over (ι.obj S))]
variable [(slicePost ι S).IsCocontinuous (J.over S) (Scheme.fppfTopology.over (ι.obj S))]
variable [HasWeakSheafify (Scheme.fppfTopology.over (ι.obj S)) (Type u)]
variable [∀ P : (Over S)ᵒᵖ ⥤ Type u, (slicePost ι S).op.HasLeftKanExtension P]
variable [PreservesFiniteLimits
  ((slicePost ι S).sheafPullback (Type u) (J.over S)
    (Scheme.fppfTopology.over (ι.obj S)))]
variable [HasPullbacks (Sheaf (J.over S) (Type u))]
variable [HasPullbacks (Over S)] [HasEqualizers (Over S)]
variable [PreservesLimitsOfShape WalkingCospan (slicePost ι S)]
variable [PreservesLimitsOfShape WalkingParallelPair (slicePost ι S)]
variable [Small.{w} (Over (ι.obj S))]

/-- The canonical inverse-image stack of the small-site quotient `[U/R]`. -/
def smallQuotientInverseImage (G : GroupoidOnSlice ι J S) :
    StackOver.InverseImage (Scheme.fppfTopology.over (ι.obj S)) (slicePost ι S)
      (sliceQuotientStack ι J S G).toStackOver :=
  StackOver.InverseImage.canonical (slicePost ι S)

/-- The small-site stackification comparison, as a cartesian based functor. -/
def sliceQuotientStackComparison (G : GroupoidOnSlice ι J S) :
    CartesianBasedFunctor (slicePrestack ι J S G).p (sliceQuotientStack ι J S G).p :=
  (sliceQuotientStackPresentation ι J S G).comparison

/-- The small-site stackification comparison inverts pushforward fractions along
`slicePost ι S`. -/
theorem sliceQuotientStackComparison_inverts (G : GroupoidOnSlice ι J S) :
    Functor.Pushforward.sourceMap.inverts (slicePost ι S)
      (sliceQuotientStackComparison ι J S G) :=
  Functor.Pushforward.sourceMap.inverts.spec (slicePost ι S)
    (sliceQuotientStackComparison ι J S G)

/-- The raw pushforward projection choice for the contained-site prestack. -/
theorem slicePrestackRawPushforwardChoice (G : GroupoidOnSlice ι J S) :
    Functor.Pushforward.ProjectionChoice (slicePost ι S) (slicePrestack ι J S G).p :=
  Functor.Pushforward.ProjectionChoice.canonical (slicePost ι S) (slicePrestack ι J S G).p

/-- The heterogeneous 04WR comparison from `u_p[U/_p R]` to `f⁻¹[U/R]`. -/
def inverseImagePushforwardComparison (G : GroupoidOnSlice ι J S) :
    CartesianBasedFunctor (sliceInverseImagePrestack ι J S G).p
      (smallQuotientInverseImage ι J S G).target.p :=
  StackOver.InverseImage.Cartesian.pushforwardComparison
    (smallQuotientInverseImage ι J S G)
    (slicePrestackRawPushforwardChoice ι J S G)
    (sliceQuotientStackComparison ι J S G)
    (sliceQuotientStackComparison_inverts ι J S G)

/-- The 04WR comparison is a stackification of `u_p[U/_p R]`. -/
theorem inverseImagePushforwardComparison_isStackification (G : GroupoidOnSlice ι J S) :
    CartesianBasedFunctor.IsStackification (Scheme.fppfTopology.over (ι.obj S))
      (inverseImagePushforwardComparison ι J S G) :=
  StackOver.InverseImage.Cartesian.pushforwardComparison.isStackification
    (smallQuotientInverseImage ι J S G)
    (sliceQuotientStack_isStackification ι J S G)
    (slicePrestackRawPushforwardChoice ι J S G)
    (sliceQuotientStackComparison_inverts ι J S G)

/-- An object `(T', φ, x)` of `u_pp[U/_p R]`, sent to the point `x ∘ φ` of the inverse-image
prestack `[f⁻¹U/_p f⁻¹R]`. -/
def pushforwardSourceToInverseImageObj (G : GroupoidOnSlice ι J S)
    (Y : Functor.pushforwardSource (slicePost ι S) (slicePrestack ι J S G).p) :
    ∫ᶜ ((G.inverseImage.points ⋙ Grpd.forgetToCat).toPseudofunctor') where
  base := Y.fst.left
  fiber :=
    ofOverMap (Y.fst.hom : Y.fst.left ⟶ (slicePost ι S).obj Y.fst.right) ≫
      OnSlice.sectionPoint ι J S G.U Y.fst.right
        (G.U.sheaf.obj.map Y.iso.hom.op Y.snd.fiber)

/-- A morphism `(a, a', α)` of `u_pp[U/_p R]`, sent to the inverse-image arrow `α ∘ φ₁`. -/
def pushforwardSourceToInverseImageMap (G : GroupoidOnSlice ι J S)
    {Y Z : Functor.pushforwardSource (slicePost ι S) (slicePrestack ι J S G).p}
    (f : Y ⟶ Z) :
    pushforwardSourceToInverseImageObj ι J S G Y ⟶
      pushforwardSourceToInverseImageObj ι J S G Z where
  base := f.fst.left
  fiber :=
    { arrow :=
        ofOverMap (Y.fst.hom : Y.fst.left ⟶ (slicePost ι S).obj Y.fst.right) ≫
          OnSlice.sectionPoint ι J S G.R Y.fst.right
            (G.R.sheaf.obj.map Y.iso.hom.op f.snd.fiber.arrow)
      source := sorry
      target := sorry }

/-- The explicit prelocalized functor `u_pp[U/_p R] ⟶ [f⁻¹U/_p f⁻¹R]` of the proof of
Lemma 78.28.1. -/
def pushforwardSourceToInverseImageFunctor (G : GroupoidOnSlice ι J S) :
    Functor.pushforwardSource (slicePost ι S) (slicePrestack ι J S G).p ⥤
      ∫ᶜ ((G.inverseImage.points ⋙ Grpd.forgetToCat).toPseudofunctor') where
  obj := pushforwardSourceToInverseImageObj ι J S G
  map := pushforwardSourceToInverseImageMap ι J S G
  map_id := sorry
  map_comp := sorry

/-- The explicit prelocalized functor inverts the pushforward fractions, so it descends to
`u_p[U/_p R]`. -/
theorem pushforwardSourceToInverseImageFunctor_inverts (G : GroupoidOnSlice ι J S) :
    ((slicePost ι S).pushforwardFractions (slicePrestack ι J S G).p).IsInvertedBy
      (pushforwardSourceToInverseImageFunctor ι J S G) := sorry

/-- The explicit cartesian functor `u_p[U/_p R] ⟶ [f⁻¹U/_p f⁻¹R]` obtained by descending
`(T', φ, x) ↦ x ∘ φ` through the localization at pushforward fractions. -/
def pushforwardToInverseImagePrestack (G : GroupoidOnSlice ι J S) :
    CartesianBasedFunctor (sliceInverseImagePrestack ι J S G).p (prestack G.inverseImage).p :=
  CartesianBasedFunctor.ofBasedFunctor
    (BasedFunctor.ofFunctor
      (Localization.Construction.lift
        (pushforwardSourceToInverseImageFunctor ι J S G)
        (pushforwardSourceToInverseImageFunctor_inverts ι J S G))
      sorry)
    sorry

/-- The source-level comparison of Lemma 78.28.1, after stackifying the inverse-image
prestack: `u_p[U/_p R] ⟶ [f⁻¹U/f⁻¹R]`. -/
def pushforwardToInverseImageQuotient (G : GroupoidOnSlice ι J S) :
    CartesianBasedFunctor (sliceInverseImagePrestack ι J S G).p
      (fppfQuotientStack G.inverseImage).p :=
  (pushforwardToInverseImagePrestack ι J S G).comp
    (fppfQuotientStackPresentation G.inverseImage).comparison

/-- The stackification lift of `pushforwardToInverseImageQuotient` through the 04WR
comparison `u_p[U/_p R] ⟶ f⁻¹[U/R]`. -/
def quotientStackInverseImageLift (G : GroupoidOnSlice ι J S) :
    CartesianBasedFunctor.IsStackification.LiftChoice
      (i := inverseImagePushforwardComparison ι J S G)
      (pushforwardToInverseImageQuotient ι J S G) :=
  CartesianBasedFunctor.IsStackification.liftChoice
    (inverseImagePushforwardComparison_isStackification ι J S G)
    (pushforwardToInverseImageQuotient ι J S G)

/-- The displayed morphism `f⁻¹[U/R] ⟶ [f⁻¹U/f⁻¹R]` of stacks in groupoids over
`(Sch'/S)_fppf`, obtained by stackifying the explicit functor `(T', φ, x) ↦ x ∘ φ`.
The book arrow `[f⁻¹U/f⁻¹R] ⟶ f⁻¹[U/R]` is its quasi-inverse. -/
def quotientStackInverseImageHom (G : GroupoidOnSlice ι J S) :
    CartesianBasedFunctor (smallQuotientInverseImage ι J S G).target.p
      (fppfQuotientStack G.inverseImage).p :=
  (quotientStackInverseImageLift ι J S G).lift

/-- The source of the displayed comparison is the inverse-image stack `f⁻¹[U/R]`. -/
theorem quotientStackInverseImageHom_source (G : GroupoidOnSlice ι J S) :
    smallQuotientInverseImage ι J S G =
      StackOver.InverseImage.canonical (slicePost ι S) := sorry

/-- The target of the displayed comparison is the quotient stack `[f⁻¹U/f⁻¹R]` of the
inverse-image groupoid. -/
theorem quotientStackInverseImageHom_target (G : GroupoidOnSlice ι J S) :
    fppfQuotientStack G.inverseImage = (fppfQuotientStackPresentation G.inverseImage).target := sorry

/-- The canonical inverse-image stack of `[U/R]` is a stackification of `u_p[U/_p R]`. -/
theorem smallQuotientInverseImage_spec (G : GroupoidOnSlice ι J S) :
    CartesianBasedFunctor.IsStackification (Scheme.fppfTopology.over (ι.obj S))
      (smallQuotientInverseImage ι J S G).comparison :=
  StackOver.InverseImage.canonical_spec (slicePost ι S)

/-- The displayed comparison is the stackification lift of the explicit proof functor through
the 04WR comparison. -/
def quotientStackInverseImageHom_comp (G : GroupoidOnSlice ι J S) :
    (CartesianBasedFunctor.precomp (fppfQuotientStack G.inverseImage).p
          (inverseImagePushforwardComparison ι J S G)).obj
        (quotientStackInverseImageHom ι J S G) ≅
      pushforwardToInverseImageQuotient ι J S G :=
  (quotientStackInverseImageLift ι J S G).comparison

end AlgebraicGeometry.GroupoidAlgebraicSpace
