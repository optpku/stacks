/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Algebraic
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Composition
public import ReasLib.CategoryTheory.Fibered.CoGrothendieck.Presheaf
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
public import stacks_project.Chap78.Definition_78_11_1_Groupoid
public import stacks_project.Chap94.Lemma_94_16_2_Presentation
public import stacks_project.Chap94.Theorem_94_17_3
public import stacks_project.Chap100.«100_3_6_1»
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.FullSubbicategory
public import stacks_project.Chap100.Lemma_100_3_6_Comparison

/-!
# Pullback of a presentation along a morphism representable by algebraic spaces

If `g : X' ⟶ X` is representable by algebraic spaces and `P` is a presentation of `X`, the
2-fibre product `U' = U ×_X X'` is an algebraic space, the kernel-pair groupoid of
`U' ⟶ X'` presents `X'`, and the projections `U' ⟶ U` and `R' ⟶ R` induce a morphism of
groupoids whose Chap94 quotient-stack map 2-commutes with `g`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupoidAlgebraicSpace
open FiberedCategoryOver.Groupoids Functor Opposite Bicategory BasedNatIso
open scoped Bicategory CategoryTheory.TwoFibreProduct Pseudofunctor.StrongTrans

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace Presentation

variable {S : Scheme.{u}} {X X' : GroupoidsOver S} [AlgebraicStack X]

/-- The atlas `1`-morphism `U ⟶ X` of a presentation, as the composite of the quotient-stack
atlas with the presenting equivalence. -/
def atlas (P : Presentation X) : P.groupoid.U.left.toGroupoids ⟶ X :=
  P.groupoid.atlas ≫ P.hom

/-- `atlas` is the composite of the quotient-stack atlas with the presenting equivalence. -/
theorem atlas_eq (P : Presentation X) :
    P.atlas = P.groupoid.atlas ≫ P.hom :=
  sorry

/-- The object space of a presentation, viewed as a groupoid fibration, is representable by an
algebraic space. -/
abbrev atlas_isRepresentable (P : Presentation X) :
    IsRepresentableByAlgebraicSpace (P.groupoid.U.left.toGroupoids) :=
  IsRepresentableByAlgebraicSpace.of_toGroupoids P.groupoid.U.left

/-- The pulled-back object space `U' = U ×_X X'`. -/
def pullbackObject (P : Presentation X) (g : X' ⟶ X) : GroupoidsOver S :=
  TwoFibreProduct.apex.{u + 1, u, u + 1, u} P.atlas g

/-- `pullbackObject` is the chosen 2-fibre product of the atlas against `g`. -/
theorem pullbackObject_eq (P : Presentation X) (g : X' ⟶ X) :
    P.pullbackObject g = TwoFibreProduct.apex.{u + 1, u, u + 1, u} P.atlas g :=
  sorry

/-- The projection `pr_U : U' ⟶ U`. -/
def objectProjection (P : Presentation X) (g : X' ⟶ X) :
    P.pullbackObject g ⟶ P.groupoid.U.left.toGroupoids :=
  TwoFibreProduct.fst.{u + 1, u, u + 1, u} P.atlas g

/-- `objectProjection` is the first projection of the 2-fibre product of the atlas against
`g`. -/
theorem objectProjection_eq (P : Presentation X) (g : X' ⟶ X) :
    P.objectProjection g = TwoFibreProduct.fst.{u + 1, u, u + 1, u} P.atlas g :=
  sorry

/-- The pulled-back atlas `U' ⟶ X'`. -/
def pullbackAtlas (P : Presentation X) (g : X' ⟶ X) : P.pullbackObject g ⟶ X' :=
  TwoFibreProduct.snd.{u + 1, u, u + 1, u} P.atlas g

/-- `pullbackAtlas` is the second projection of the 2-fibre product of the atlas against `g`. -/
theorem pullbackAtlas_eq (P : Presentation X) (g : X' ⟶ X) :
    P.pullbackAtlas g = TwoFibreProduct.snd.{u + 1, u, u + 1, u} P.atlas g :=
  sorry

/-- The structure morphism `R ⟶ X` of the arrow space of a presentation, as the target map
followed by the atlas. -/
def arrowToX (P : Presentation X) : P.groupoid.R.left.toGroupoids ⟶ X :=
  toGroupoids.map P.groupoid.t.left ≫ P.atlas

/-- `arrowToX` is the target map of the presenting groupoid followed by the atlas. -/
theorem arrowToX_eq (P : Presentation X) :
    P.arrowToX = toGroupoids.map P.groupoid.t.left ≫ P.atlas :=
  sorry

/-- The pulled-back arrow space `R' = R ×_X X'`. -/
def arrowBaseChange (P : Presentation X) (g : X' ⟶ X) : GroupoidsOver S :=
  TwoFibreProduct.apex.{u + 1, u, u + 1, u} P.arrowToX g

/-- `arrowBaseChange` is the chosen 2-fibre product of `arrowToX` against `g`. -/
theorem arrowBaseChange_eq (P : Presentation X) (g : X' ⟶ X) :
    P.arrowBaseChange g = TwoFibreProduct.apex.{u + 1, u, u + 1, u} P.arrowToX g :=
  sorry

/-- Space-representability of `U' = U ×_X X'`, obtained by base change of the atlas along a
morphism representable by algebraic spaces. -/
abbrev pullbackObject_isRepresentable (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g) :
    IsRepresentableByAlgebraicSpace (P.pullbackObject g) :=
  IsRepresentableByAlgebraicSpace.twoFibreProduct g P.atlas hg P.atlas_isRepresentable

/-- The atlas of a presentation is a smooth `1`-morphism of groupoid fibrations. -/
instance instSmooth_atlas (P : Presentation X) : Groupoids.Hom.Smooth P.atlas :=
  sorry

/-- The atlas of a presentation is a surjective `1`-morphism of groupoid fibrations. -/
instance instSurjective_atlas (P : Presentation X) : Groupoids.Hom.Surjective P.atlas :=
  sorry

/-- The presenting groupoid of a presentation is smooth. -/
instance instSmooth_groupoid (P : Presentation X) :
    GroupoidAlgebraicSpace.Smooth P.groupoid :=
  P.isSmooth

variable [AlgebraicStack X']

/-- The pulled-back atlas `U' ⟶ X'` is smooth. -/
instance instSmooth_pullbackAtlas (P : Presentation X) (g : X' ⟶ X) :
    Groupoids.Hom.Smooth (P.pullbackAtlas g) :=
  sorry

/-- The pulled-back atlas `U' ⟶ X'` is surjective. -/
instance instSurjective_pullbackAtlas (P : Presentation X) (g : X' ⟶ X) :
    Groupoids.Hom.Surjective (P.pullbackAtlas g) :=
  sorry

/-- The kernel-pair groupoid `(U', R', s', t', c')` of the pulled-back atlas. -/
abbrev pullbackGroupoid (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g) :
    GroupoidAlgebraicSpace (ofOver (Over.mk (𝟙 S))) :=
  AlgebraicStack.groupoid (P.pullbackAtlas g) (P.pullbackObject_isRepresentable g hg)

/-- `pullbackGroupoid` is the kernel-pair groupoid of the pulled-back atlas. -/
theorem pullbackGroupoid_eq (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g) :
    P.pullbackGroupoid g hg =
      AlgebraicStack.groupoid (P.pullbackAtlas g) (P.pullbackObject_isRepresentable g hg) :=
  sorry

/-- The fibre morphism of `[U /ₚ R]` associated to an `R`-point, with underlying arrow that
point itself. -/
def groupoid_sourceTargetPreHom (P : Presentation X)
    (x : P.groupoid.R.left.toGroupoids.total) :
    (toFunctor
        (toGroupoids.map P.groupoid.s.left ≫ P.groupoid.atlasToPreQuotient)).obj x ⟶
      (toFunctor
        (toGroupoids.map P.groupoid.t.left ≫ P.groupoid.atlasToPreQuotient)).obj x where
  base := 𝟙 _
  fiber := FunctorPointHom.ofArrow x.unop.snd sorry sorry

/-- The inverse fibre morphism of `[U /ₚ R]` associated to an `R`-point, with underlying arrow
the groupoid inverse of that point. -/
def groupoid_sourceTargetPreInvHom (P : Presentation X)
    (x : P.groupoid.R.left.toGroupoids.total) :
    (toFunctor
        (toGroupoids.map P.groupoid.t.left ≫ P.groupoid.atlasToPreQuotient)).obj x ⟶
      (toFunctor
        (toGroupoids.map P.groupoid.s.left ≫ P.groupoid.atlasToPreQuotient)).obj x where
  base := 𝟙 _
  fiber :=
    FunctorPointHom.ofArrow
      (P.groupoid.i.left.app (op x.unop.fst.unop) x.unop.snd) sorry sorry

/-- Componentwise `2`-isomorphism `πₚ ∘ s ≅ πₚ ∘ t` on `[U /ₚ R]`. -/
def groupoid_sourceTargetPreApp (P : Presentation X)
    (x : P.groupoid.R.left.toGroupoids.total) :
    (toFunctor
        (toGroupoids.map P.groupoid.s.left ≫ P.groupoid.atlasToPreQuotient)).obj x ≅
      (toFunctor
        (toGroupoids.map P.groupoid.t.left ≫ P.groupoid.atlasToPreQuotient)).obj x where
  hom := P.groupoid_sourceTargetPreHom x
  inv := P.groupoid_sourceTargetPreInvHom x
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The canonical `2`-isomorphism `s ≫ atlasToPreQuotient ≅ t ≫ atlasToPreQuotient` of the
presenting groupoid, assembled from the fibre arrows of `R`. -/
def groupoid_preAtlas_sourceTargetIso (P : Presentation X) :
    toGroupoids.map P.groupoid.s.left ≫ P.groupoid.atlasToPreQuotient ≅
      toGroupoids.map P.groupoid.t.left ≫ P.groupoid.atlasToPreQuotient :=
  BasedFunctorIso.lift
    (ofComponents (P.groupoid_sourceTargetPreApp) (fun {_ _} _ ↦ sorry) (fun _ ↦ sorry))

/-- The canonical `2`-isomorphism `s ≫ atlas ≅ t ≫ atlas` on the Chap94 quotient stack of the
presenting groupoid, obtained by whiskering the prestack cell by stackification. -/
def groupoid_atlas_sourceTargetIso (P : Presentation X) :
    toGroupoids.map P.groupoid.s.left ≫ P.groupoid.atlas ≅
      toGroupoids.map P.groupoid.t.left ≫ P.groupoid.atlas :=
  (α_ (toGroupoids.map P.groupoid.s.left) P.groupoid.atlasToPreQuotient
      P.groupoid.stackificationHom).symm ≪≫
    whiskerRightIso (P.groupoid_preAtlas_sourceTargetIso) P.groupoid.stackificationHom ≪≫
    α_ (toGroupoids.map P.groupoid.t.left) P.groupoid.atlasToPreQuotient
      P.groupoid.stackificationHom

/-- The canonical `2`-isomorphism `s ≫ P.atlas ≅ t ≫ P.atlas`, obtained by whiskering the
quotient-stack cell of the presenting groupoid by `P.hom`. -/
def atlas_sourceTargetIso (P : Presentation X) :
    toGroupoids.map P.groupoid.s.left ≫ P.atlas ≅
      toGroupoids.map P.groupoid.t.left ≫ P.atlas :=
  (α_ (toGroupoids.map P.groupoid.s.left) P.groupoid.atlas P.hom).symm ≪≫
    whiskerRightIso (P.groupoid_atlas_sourceTargetIso) P.hom ≪≫
    α_ (toGroupoids.map P.groupoid.t.left) P.groupoid.atlas P.hom

/-- The presenting equivalence `P.hom : [U / R] ⟶ X`, packaged as a bicategorical
equivalence from the real field `P.isEquivalence`. -/
def presentationEquiv (P : Presentation X) :
    P.groupoid.quotientStack ≌ X :=
  ObjectProperty.FullSubbicategory.asEquivalenceOf P.hom P.isEquivalence

/-- The chosen inverse `X ⟶ [U / R]` of the presenting equivalence. -/
def presentationInv (P : Presentation X) : X ⟶ P.groupoid.quotientStack :=
  P.presentationEquiv.inv

/-- The unit cell `𝟙_[U / R] ≅ P.hom ≫ presentationInv`. -/
def presentation_unitIso (P : Presentation X) :
    𝟙 P.groupoid.quotientStack ≅ P.hom ≫ P.presentationInv :=
  P.presentationEquiv.unit

/-- Cospan transformation `(P.atlas, P.atlas) ⟶ (P.groupoid.atlas, P.groupoid.atlas)` with
identity object maps and base `presentationInv`. -/
def atlasToQuotientCospan (P : Presentation X) :
    CospanTransform P.atlas P.atlas P.groupoid.atlas P.groupoid.atlas :=
  CospanTransform.mk (𝟙 _) (𝟙 _) P.presentationInv
    ((λ_ P.groupoid.atlas) ≪≫ (ρ_ P.groupoid.atlas).symm ≪≫
      whiskerLeftIso P.groupoid.atlas P.presentation_unitIso ≪≫
      (α_ P.groupoid.atlas P.hom P.presentationInv).symm)
    ((λ_ P.groupoid.atlas) ≪≫ (ρ_ P.groupoid.atlas).symm ≪≫
      whiskerLeftIso P.groupoid.atlas P.presentation_unitIso ≪≫
      (α_ P.groupoid.atlas P.hom P.presentationInv).symm)

/-- Comparison `U ×_X U ⟶ U ×_{[U / R]} U` induced by the presenting equivalence. -/
def atlasKernelToQuotientKernel (P : Presentation X) :
    kernelPair P.atlas ⟶ kernelPair P.groupoid.atlas :=
  TwoFibreProduct.map P.atlasToQuotientCospan

section

-- Local instance justification (proof-local temporary data): supply the anonymous quotient-algebraicity argument of kernelPair_isRepresentableByAlgebraicSpace only while elaborating groupoidKernel_isRepresentable; the enclosing section exports no instance registration.
attribute [local instance] AlgebraicGeometry.GroupoidAlgebraicSpace.instAlgebraicStack_quotientStack

/-- Space-representability of the kernel pair of the quotient-stack atlas. -/
abbrev groupoidKernel_isRepresentable (P : Presentation X) :
    IsRepresentableByAlgebraicSpace (kernelPair P.groupoid.atlas) :=
  kernelPair_isRepresentableByAlgebraicSpace P.groupoid.atlas P.atlas_isRepresentable

end

/-- The reverse comparison `U ×_X U ⟶ R`: transport to the quotient-stack kernel pair,
lift its comparison through fully faithful prestack stackification, and extract the `R`-point. -/
def atlasKernelToGroupoidArrow (P : Presentation X) :
    kernelPair P.atlas ⟶ P.groupoid.R.left.toGroupoids :=
  P.atlasKernelToQuotientKernel ≫ P.groupoid.quotientKernelToArrow

/-- The recovered arrow has target the first atlas-kernel projection. -/
def atlasKernelToGroupoidArrow_targetIso (P : Presentation X) :
    P.atlasKernelToGroupoidArrow ≫ toGroupoids.map P.groupoid.t.left ≅ pr0 P.atlas :=
  α_ P.atlasKernelToQuotientKernel P.groupoid.quotientKernelToArrow
      (toGroupoids.map P.groupoid.t.left) ≪≫
    whiskerLeftIso P.atlasKernelToQuotientKernel P.groupoid.quotientKernelToArrow_targetIso ≪≫
    TwoFibreProduct.map.fstIso P.atlasToQuotientCospan ≪≫
    ρ_ (pr0 P.atlas)

/-- The recovered arrow has source the second atlas-kernel projection. -/
def atlasKernelToGroupoidArrow_sourceIso (P : Presentation X) :
    P.atlasKernelToGroupoidArrow ≫ toGroupoids.map P.groupoid.s.left ≅ pr1 P.atlas :=
  α_ P.atlasKernelToQuotientKernel P.groupoid.quotientKernelToArrow
      (toGroupoids.map P.groupoid.s.left) ≪≫
    whiskerLeftIso P.atlasKernelToQuotientKernel P.groupoid.quotientKernelToArrow_sourceIso ≪≫
    TwoFibreProduct.map.sndIso P.atlasToQuotientCospan ≪≫
    ρ_ (pr1 P.atlas)

/-- Cospan transformation `(arrowToX, g) ⟶ (atlas, g)` induced by the target map of the
presenting groupoid. -/
def arrowBaseChangeCospan_t (P : Presentation X) (g : X' ⟶ X) :
    CospanTransform P.arrowToX g P.atlas g :=
  CospanTransform.mk (toGroupoids.map P.groupoid.t.left) (𝟙 X') (𝟙 X)
    (ρ_ P.arrowToX).symm (λ_ g ≪≫ (ρ_ g).symm)

/-- Cospan transformation `(arrowToX, g) ⟶ (atlas, g)` induced by the source map of the
presenting groupoid. -/
def arrowBaseChangeCospan_s (P : Presentation X) (g : X' ⟶ X) :
    CospanTransform P.arrowToX g P.atlas g :=
  CospanTransform.mk (toGroupoids.map P.groupoid.s.left) (𝟙 X') (𝟙 X)
    (atlas_sourceTargetIso P ≪≫ (ρ_ P.arrowToX).symm) (λ_ g ≪≫ (ρ_ g).symm)

/-- The map `R ×_X X' ⟶ U ×_X X'` induced by the target map `R ⟶ U`. -/
def arrowBaseChange_viaTarget (P : Presentation X) (g : X' ⟶ X) :
    P.arrowBaseChange g ⟶ P.pullbackObject g :=
  TwoFibreProduct.map (P.arrowBaseChangeCospan_t g)

/-- The map `R ×_X X' ⟶ U ×_X X'` induced by the source map `R ⟶ U`. -/
def arrowBaseChange_viaSource (P : Presentation X) (g : X' ⟶ X) :
    P.arrowBaseChange g ⟶ P.pullbackObject g :=
  TwoFibreProduct.map (P.arrowBaseChangeCospan_s g)

/-- The cone exhibiting `R ×_X X'` as a `2`-fibre product of the pulled-back atlas with
itself. -/
def arrowBaseChangeAsKernelCone (P : Presentation X) (g : X' ⟶ X) :
    PseudoPullbackCone (P.pullbackAtlas g) (P.pullbackAtlas g) where
  pt := P.arrowBaseChange g
  fst := P.arrowBaseChange_viaTarget g
  snd := P.arrowBaseChange_viaSource g
  iso :=
    TwoFibreProduct.map.sndIso (P.arrowBaseChangeCospan_t g) ≪≫
      (TwoFibreProduct.map.sndIso (P.arrowBaseChangeCospan_s g)).symm

/-- The cone `arrowBaseChangeAsKernelCone` is a bilimit. This is a theorem, not an instance
consumed by universal lifts. -/
theorem isBilimit_arrowBaseChangeAsKernelCone (P : Presentation X) (g : X' ⟶ X) :
    (P.arrowBaseChangeAsKernelCone g).IsBilimit :=
  sorry

/-- Comparison `1`-morphism `R ×_X X' ⟶ U' ×_{X'} U'` from the source fibre product of arrow
spaces to the kernel pair of the pulled-back atlas, as the universal lift into the genuine
2-fibre product of the pulled-back atlas with itself. -/
def arrowBaseChangeToKernelPair (P : Presentation X) (g : X' ⟶ X) :
    P.arrowBaseChange g ⟶ kernelPair (P.pullbackAtlas g) :=
  PseudoPullbackCone.lift (P.arrowBaseChangeAsKernelCone g)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} (P.pullbackAtlas g) (P.pullbackAtlas g))

/-- `arrowBaseChangeToKernelPair` followed by the first projection of `U' ×_{X'} U'` is
2-isomorphic to the target-induced map `R ×_X X' ⟶ U'`. -/
def arrowBaseChangeToKernelPair_fstIso (P : Presentation X) (g : X' ⟶ X) :
    P.arrowBaseChangeToKernelPair g ≫ pr0 (P.pullbackAtlas g) ≅
      P.arrowBaseChange_viaTarget g :=
  PseudoPullbackCone.lift.fstIso (P.arrowBaseChangeAsKernelCone g)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} (P.pullbackAtlas g) (P.pullbackAtlas g))

/-- `arrowBaseChangeToKernelPair` followed by the second projection of `U' ×_{X'} U'` is
2-isomorphic to the source-induced map `R ×_X X' ⟶ U'`. -/
def arrowBaseChangeToKernelPair_sndIso (P : Presentation X) (g : X' ⟶ X) :
    P.arrowBaseChangeToKernelPair g ≫ pr1 (P.pullbackAtlas g) ≅
      P.arrowBaseChange_viaSource g :=
  PseudoPullbackCone.lift.sndIso (P.arrowBaseChangeAsKernelCone g)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} (P.pullbackAtlas g) (P.pullbackAtlas g))

/-- The projection `pr_R : R' ⟶ R` of `R ×_X X'`, as a `1`-morphism of groupoid fibrations. -/
def arrowProjectionToGroupoid (P : Presentation X) (g : X' ⟶ X) :
    P.arrowBaseChange g ⟶ P.groupoid.R.left.toGroupoids :=
  TwoFibreProduct.fst.{u + 1, u, u + 1, u} P.arrowToX g

/-- `arrowProjectionToGroupoid` is the first projection of `R ×_X X'`. -/
theorem arrowProjectionToGroupoid_eq (P : Presentation X) (g : X' ⟶ X) :
    P.arrowProjectionToGroupoid g =
      TwoFibreProduct.fst.{u + 1, u, u + 1, u} P.arrowToX g :=
  sorry

/-- The structure morphism `(U ×_X U) ⟶ X` of the kernel pair of the atlas. -/
def atlasKernelToX (P : Presentation X) : kernelPair P.atlas ⟶ X :=
  TwoFibreProduct.fst.{u + 1, u, u + 1, u} P.atlas P.atlas ≫ P.atlas

/-- `atlasKernelToX` is the first kernel-pair projection followed by the atlas. -/
theorem atlasKernelToX_eq (P : Presentation X) :
    P.atlasKernelToX =
      TwoFibreProduct.fst.{u + 1, u, u + 1, u} P.atlas P.atlas ≫ P.atlas :=
  sorry

/-- The iterated fibre product `(U ×_X U) ×_X X'`. -/
def atlasKernelBaseChange (P : Presentation X) (g : X' ⟶ X) : GroupoidsOver S :=
  TwoFibreProduct.apex.{u + 1, u, u + 1, u} P.atlasKernelToX g

/-- `atlasKernelBaseChange` is the chosen 2-fibre product of `atlasKernelToX` against `g`. -/
theorem atlasKernelBaseChange_eq (P : Presentation X) (g : X' ⟶ X) :
    P.atlasKernelBaseChange g =
      TwoFibreProduct.apex.{u + 1, u, u + 1, u} P.atlasKernelToX g :=
  sorry

/-- The cone exhibiting `U' ×_{X'} U'` as a 2-fibre product of `atlasKernelToX` against `g`,
with first leg `arrowProjection` and second leg the pulled-back atlas on the second factor.
The comparison cell is assembled from `selfComparison_whisker_eq P.atlas g`. -/
def kernelPairAsAtlasKernelBaseChangeCone (P : Presentation X) (g : X' ⟶ X) :
    PseudoPullbackCone P.atlasKernelToX g where
  pt := kernelPair (P.pullbackAtlas g)
  fst := AlgebraicGeometry.Groupoids.arrowProjection P.atlas g
  snd :=
    TwoFibreProduct.snd.{u + 1, u, u + 1, u} (P.pullbackAtlas g) (P.pullbackAtlas g) ≫
      P.pullbackAtlas g
  iso :=
    whiskerRightIso
        (TwoFibreProduct.map.fstIso
          (AlgebraicGeometry.Groupoids.selfFibreCospan P.atlas g))
        P.atlas ≪≫
      α_ (TwoFibreProduct.fst.{u + 1, u, u + 1, u} (P.pullbackAtlas g) (P.pullbackAtlas g))
        (TwoFibreProduct.fst.{u + 1, u, u + 1, u} P.atlas g) P.atlas ≪≫
      whiskerLeftIso
        (TwoFibreProduct.fst.{u + 1, u, u + 1, u} (P.pullbackAtlas g) (P.pullbackAtlas g))
        (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} P.atlas g) ≪≫
      (α_ (TwoFibreProduct.fst.{u + 1, u, u + 1, u} (P.pullbackAtlas g) (P.pullbackAtlas g))
        (P.pullbackAtlas g) g).symm ≪≫
      whiskerRightIso
        (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u}
          (P.pullbackAtlas g) (P.pullbackAtlas g))
        g ≪≫
      α_ (TwoFibreProduct.snd.{u + 1, u, u + 1, u} (P.pullbackAtlas g) (P.pullbackAtlas g))
        (P.pullbackAtlas g) g

/-- Associativity comparison `U' ×_{X'} U' ⟶ (U ×_X U) ×_X X'`, as the universal lift into
the genuine 2-fibre product of `atlasKernelToX` against `g`. -/
def kernelPairToAtlasKernelBaseChange (P : Presentation X) (g : X' ⟶ X) :
    kernelPair (P.pullbackAtlas g) ⟶ P.atlasKernelBaseChange g :=
  PseudoPullbackCone.lift (P.kernelPairAsAtlasKernelBaseChangeCone g)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} P.atlasKernelToX g)

/-- `kernelPairToAtlasKernelBaseChange` followed by the first projection of
`(U ×_X U) ×_X X'` is 2-isomorphic to `arrowProjection`. -/
def kernelPairToAtlasKernelBaseChange_fstIso (P : Presentation X) (g : X' ⟶ X) :
    P.kernelPairToAtlasKernelBaseChange g ≫
        TwoFibreProduct.fst.{u + 1, u, u + 1, u} P.atlasKernelToX g ≅
      AlgebraicGeometry.Groupoids.arrowProjection P.atlas g :=
  PseudoPullbackCone.lift.fstIso (P.kernelPairAsAtlasKernelBaseChangeCone g)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} P.atlasKernelToX g)

/-- `kernelPairToAtlasKernelBaseChange` followed by the second projection of
`(U ×_X U) ×_X X'` is 2-isomorphic to the pulled-back atlas on the second factor. -/
def kernelPairToAtlasKernelBaseChange_sndIso (P : Presentation X) (g : X' ⟶ X) :
    P.kernelPairToAtlasKernelBaseChange g ≫
        TwoFibreProduct.snd.{u + 1, u, u + 1, u} P.atlasKernelToX g ≅
      TwoFibreProduct.snd.{u + 1, u, u + 1, u} (P.pullbackAtlas g) (P.pullbackAtlas g) ≫
        P.pullbackAtlas g :=
  PseudoPullbackCone.lift.sndIso (P.kernelPairAsAtlasKernelBaseChangeCone g)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} P.atlasKernelToX g)

/-- Cospan transformation `((U ×_X U) ⟶ X, g) ⟶ (atlas, g)` induced by the first kernel-pair
projection. -/
def atlasKernelBaseChangeCospan_fst (P : Presentation X) (g : X' ⟶ X) :
    CospanTransform P.atlasKernelToX g P.atlas g :=
  CospanTransform.mk
    (TwoFibreProduct.fst.{u + 1, u, u + 1, u} P.atlas P.atlas) (𝟙 X') (𝟙 X)
    (ρ_ P.atlasKernelToX).symm (λ_ g ≪≫ (ρ_ g).symm)

/-- Cospan transformation `((U ×_X U) ⟶ X, g) ⟶ (atlas, g)` induced by the second kernel-pair
projection. -/
def atlasKernelBaseChangeCospan_snd (P : Presentation X) (g : X' ⟶ X) :
    CospanTransform P.atlasKernelToX g P.atlas g :=
  CospanTransform.mk
    (TwoFibreProduct.snd.{u + 1, u, u + 1, u} P.atlas P.atlas) (𝟙 X') (𝟙 X)
    ((TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} P.atlas P.atlas).symm ≪≫
      (ρ_ P.atlasKernelToX).symm)
    (λ_ g ≪≫ (ρ_ g).symm)

/-- The map `(U ×_X U) ×_X X' ⟶ U'` induced by the first kernel-pair projection. -/
def atlasKernelBaseChange_viaTarget (P : Presentation X) (g : X' ⟶ X) :
    P.atlasKernelBaseChange g ⟶ P.pullbackObject g :=
  TwoFibreProduct.map (P.atlasKernelBaseChangeCospan_fst g)

/-- The map `(U ×_X U) ×_X X' ⟶ U'` induced by the second kernel-pair projection. -/
def atlasKernelBaseChange_viaSource (P : Presentation X) (g : X' ⟶ X) :
    P.atlasKernelBaseChange g ⟶ P.pullbackObject g :=
  TwoFibreProduct.map (P.atlasKernelBaseChangeCospan_snd g)

/-- The cone exhibiting `(U ×_X U) ×_X X'` as a 2-fibre product of the pulled-back atlas with
itself. -/
def atlasKernelBaseChangeAsKernelCone (P : Presentation X) (g : X' ⟶ X) :
    PseudoPullbackCone (P.pullbackAtlas g) (P.pullbackAtlas g) where
  pt := P.atlasKernelBaseChange g
  fst := P.atlasKernelBaseChange_viaTarget g
  snd := P.atlasKernelBaseChange_viaSource g
  iso :=
    TwoFibreProduct.map.sndIso (P.atlasKernelBaseChangeCospan_fst g) ≪≫
      (TwoFibreProduct.map.sndIso (P.atlasKernelBaseChangeCospan_snd g)).symm

/-- Reverse associativity comparison `(U ×_X U) ×_X X' ⟶ U' ×_{X'} U'`, as the universal lift
into the genuine 2-fibre product of the pulled-back atlas with itself. -/
def atlasKernelBaseChangeToKernelPair (P : Presentation X) (g : X' ⟶ X) :
    P.atlasKernelBaseChange g ⟶ kernelPair (P.pullbackAtlas g) :=
  PseudoPullbackCone.lift (P.atlasKernelBaseChangeAsKernelCone g)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} (P.pullbackAtlas g) (P.pullbackAtlas g))

/-- `atlasKernelBaseChangeToKernelPair` followed by the first projection of `U' ×_{X'} U'` is
2-isomorphic to `atlasKernelBaseChange_viaTarget`. -/
def atlasKernelBaseChangeToKernelPair_fstIso (P : Presentation X) (g : X' ⟶ X) :
    P.atlasKernelBaseChangeToKernelPair g ≫ pr0 (P.pullbackAtlas g) ≅
      P.atlasKernelBaseChange_viaTarget g :=
  PseudoPullbackCone.lift.fstIso (P.atlasKernelBaseChangeAsKernelCone g)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} (P.pullbackAtlas g) (P.pullbackAtlas g))

/-- `atlasKernelBaseChangeToKernelPair` followed by the second projection of `U' ×_{X'} U'` is
2-isomorphic to `atlasKernelBaseChange_viaSource`. -/
def atlasKernelBaseChangeToKernelPair_sndIso (P : Presentation X) (g : X' ⟶ X) :
    P.atlasKernelBaseChangeToKernelPair g ≫ pr1 (P.pullbackAtlas g) ≅
      P.atlasKernelBaseChange_viaSource g :=
  PseudoPullbackCone.lift.sndIso (P.atlasKernelBaseChangeAsKernelCone g)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} (P.pullbackAtlas g) (P.pullbackAtlas g))

/-- The cone exhibiting the presenting arrow space as a `2`-fibre product of `P.atlas` with
itself, using the transported source/target cell of the quotient-stack square. -/
def groupoidArrowAsAtlasCone (P : Presentation X) :
    PseudoPullbackCone P.atlas P.atlas where
  pt := P.groupoid.R.left.toGroupoids
  fst := toGroupoids.map P.groupoid.t.left
  snd := toGroupoids.map P.groupoid.s.left
  iso := (P.atlas_sourceTargetIso).symm

/-- The cone `groupoidArrowAsAtlasCone` is a bilimit. This is a theorem, not an instance
consumed by universal lifts. -/
theorem isBilimit_groupoidArrowAsAtlasCone (P : Presentation X) :
    P.groupoidArrowAsAtlasCone.IsBilimit :=
  sorry

/-- Comparison `1`-morphism `R ⟶ U ×_X U` from the presenting arrow space to the kernel pair
of the atlas, as the universal lift of the source/target cone into the genuine 2-fibre product
of `P.atlas` with itself. -/
def groupoidArrowToAtlasKernel (P : Presentation X) :
    P.groupoid.R.left.toGroupoids ⟶ kernelPair P.atlas :=
  PseudoPullbackCone.lift P.groupoidArrowAsAtlasCone
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} P.atlas P.atlas)

/-- `groupoidArrowToAtlasKernel` followed by the first projection of `U ×_X U` is 2-isomorphic
to the target map of the presenting groupoid. -/
def groupoidArrowToAtlasKernel_fstIso (P : Presentation X) :
    P.groupoidArrowToAtlasKernel ≫ pr0 P.atlas ≅
      toGroupoids.map P.groupoid.t.left :=
  PseudoPullbackCone.lift.fstIso P.groupoidArrowAsAtlasCone
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} P.atlas P.atlas)

/-- `groupoidArrowToAtlasKernel` followed by the second projection of `U ×_X U` is 2-isomorphic
to the source map of the presenting groupoid. -/
def groupoidArrowToAtlasKernel_sndIso (P : Presentation X) :
    P.groupoidArrowToAtlasKernel ≫ pr1 P.atlas ≅
      toGroupoids.map P.groupoid.s.left :=
  PseudoPullbackCone.lift.sndIso P.groupoidArrowAsAtlasCone
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} P.atlas P.atlas)

/-- Cospan transformation `(arrowToX, g) ⟶ (atlasKernelToX, g)` induced by
`groupoidArrowToAtlasKernel`. -/
def groupoidArrowBaseChangeCospan (P : Presentation X) (g : X' ⟶ X) :
    CospanTransform P.arrowToX g P.atlasKernelToX g :=
  CospanTransform.mk P.groupoidArrowToAtlasKernel (𝟙 X') (𝟙 X)
    ((α_ P.groupoidArrowToAtlasKernel
        (TwoFibreProduct.fst.{u + 1, u, u + 1, u} P.atlas P.atlas) P.atlas).symm ≪≫
      whiskerRightIso P.groupoidArrowToAtlasKernel_fstIso P.atlas ≪≫
      (ρ_ P.arrowToX).symm)
    (λ_ g ≪≫ (ρ_ g).symm)

/-- The map `R ×_X X' ⟶ (U ×_X U) ×_X X'` induced by `groupoidArrowToAtlasKernel`. -/
def arrowBaseChangeToAtlasKernelBaseChange (P : Presentation X) (g : X' ⟶ X) :
    P.arrowBaseChange g ⟶ P.atlasKernelBaseChange g :=
  TwoFibreProduct.map (P.groupoidArrowBaseChangeCospan g)

/-- Inverse law for the associativity comparisons identifying `(U ×_X U) ×_X X'` with
`U' ×_{X'} U'`. -/
theorem atlasKernelBaseChangeToKernelPair_comp_kernelPairToAtlasKernelBaseChange
    (P : Presentation X) (g : X' ⟶ X) :
    Nonempty (P.atlasKernelBaseChangeToKernelPair g ≫ P.kernelPairToAtlasKernelBaseChange g ≅
      𝟙 (P.atlasKernelBaseChange g)) :=
  sorry

/-- Reverse inverse law for the associativity comparisons identifying `(U ×_X U) ×_X X'`
with `U' ×_{X'} U'`. -/
theorem kernelPairToAtlasKernelBaseChange_comp_atlasKernelBaseChangeToKernelPair
    (P : Presentation X) (g : X' ⟶ X) :
    Nonempty (P.kernelPairToAtlasKernelBaseChange g ≫ P.atlasKernelBaseChangeToKernelPair g ≅
      𝟙 (kernelPair (P.pullbackAtlas g))) :=
  sorry

/-- Space-representability of `R' = R ×_X X'`. -/
abbrev arrowBaseChange_isRepresentable (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g) :
    IsRepresentableByAlgebraicSpace (P.arrowBaseChange g) :=
  IsRepresentableByAlgebraicSpace.twoFibreProduct g P.arrowToX hg
    (IsRepresentableByAlgebraicSpace.of_toGroupoids P.groupoid.R.left)

/-- `arrowProjection` of the atlas square is the two-fibre-product map of `selfFibreCospan`,
whose comparison cell is equation 04Y7 (`selfComparison_whisker_eq`). -/
theorem pullbackPr_arrowProjection_eq (P : Presentation X) (g : X' ⟶ X) :
    AlgebraicGeometry.Groupoids.arrowProjection P.atlas g =
      TwoFibreProduct.map (AlgebraicGeometry.Groupoids.selfFibreCospan P.atlas g) :=
  sorry

/-- The pulled-back presentation `[U' / R'] ⟶ X'`. -/
def pullback (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g) : Presentation X' :=
  Presentation.ofSmoothSurjective (P.pullbackAtlas g)
    (P.pullbackObject_isRepresentable g hg)

/-- The presenting groupoid of `P.pullback` is `P.pullbackGroupoid`. -/
theorem pullback_groupoid (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g) :
    (P.pullback g hg).groupoid = P.pullbackGroupoid g hg :=
  sorry

/-- The presenting equivalence of `P.pullback` is `fCan` of the pulled-back atlas. -/
theorem pullback_hom (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g) :
    (P.pullback g hg).hom =
      AlgebraicStack.fCan (P.pullbackAtlas g) (P.pullbackObject_isRepresentable g hg) :=
  sorry

/-- Recover an `Over` morphism from a `1`-morphism of presented groupoid fibrations. -/
def overRecover {F : AlgebraicSpace S} {A B : GroupoidsOver S}
    {U : Over (ofOver (Over.mk (𝟙 S)))}
    (eA : A ≌ F.toGroupoids) (eB : B ≌ U.left.toGroupoids) (φ : A ⟶ B) :
    overS.obj F ⟶ U :=
  Over.homMk (extendBaseIdHom F ≫ toGroupoids.recover eA eB φ) sorry

/-- The object component of `pr`, recovered from `pr_U = objectProjection`. -/
def pullbackPr_obj (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g) :
    (P.pullbackGroupoid g hg).U ⟶ P.groupoid.U :=
  overRecover (representingEquiv (P.pullbackObject_isRepresentable g hg))
    (Bicategory.Equivalence.id _) (P.objectProjection g)

/-- `pullbackPr_obj` is recovered from `objectProjection`. -/
theorem pullbackPr_obj_eq (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g) :
    P.pullbackPr_obj g hg =
      overRecover (representingEquiv (P.pullbackObject_isRepresentable g hg))
        (Bicategory.Equivalence.id _) (P.objectProjection g) :=
  sorry

/-- Space-representability of the kernel pair of the pulled-back atlas. -/
abbrev pullbackKernel_isRepresentable (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g) :
    IsRepresentableByAlgebraicSpace (kernelPair (P.pullbackAtlas g)) :=
  kernelPair_isRepresentableByAlgebraicSpace (P.pullbackAtlas g)
    (P.pullbackObject_isRepresentable g hg)

/-- Inverse law for the kernel-pair comparisons of the presenting arrow space. -/
theorem groupoidArrowToAtlasKernel_comp_atlasKernelToGroupoidArrow (P : Presentation X) :
    Nonempty (P.groupoidArrowToAtlasKernel ≫ P.atlasKernelToGroupoidArrow ≅
      𝟙 P.groupoid.R.left.toGroupoids) :=
  sorry

/-- Reverse inverse law for the kernel-pair comparisons of the presenting arrow space. -/
theorem atlasKernelToGroupoidArrow_comp_groupoidArrowToAtlasKernel (P : Presentation X) :
    Nonempty (P.atlasKernelToGroupoidArrow ≫ P.groupoidArrowToAtlasKernel ≅
      𝟙 (kernelPair P.atlas)) :=
  sorry

/-- The cone from the pulled-back atlas kernel pair to `(R ⟶ X, X' ⟶ X)`, using the
recovered `R`-arrow and its explicit target comparison. -/
def kernelPairAsArrowBaseChangeCone (P : Presentation X) (g : X' ⟶ X) :
    PseudoPullbackCone P.arrowToX g where
  pt := kernelPair (P.pullbackAtlas g)
  fst := AlgebraicGeometry.Groupoids.arrowProjection P.atlas g ≫ P.atlasKernelToGroupoidArrow
  snd := (P.kernelPairAsAtlasKernelBaseChangeCone g).snd
  iso :=
    α_ (AlgebraicGeometry.Groupoids.arrowProjection P.atlas g)
        P.atlasKernelToGroupoidArrow P.arrowToX ≪≫
      whiskerLeftIso (AlgebraicGeometry.Groupoids.arrowProjection P.atlas g)
        ((α_ P.atlasKernelToGroupoidArrow (toGroupoids.map P.groupoid.t.left) P.atlas).symm ≪≫
          whiskerRightIso P.atlasKernelToGroupoidArrow_targetIso P.atlas) ≪≫
      (P.kernelPairAsAtlasKernelBaseChangeCone g).iso

/-- The actual reverse comparison `U' ×_{X'} U' ⟶ R ×_X X'`, as a lift into the genuine
two-fibre product, with both projection maps supplied by `kernelPairAsArrowBaseChangeCone`. -/
def kernelPairToArrowBaseChange (P : Presentation X) (g : X' ⟶ X) :
    kernelPair (P.pullbackAtlas g) ⟶ P.arrowBaseChange g :=
  PseudoPullbackCone.lift (P.kernelPairAsArrowBaseChangeCone g)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} P.arrowToX g)

/-- The reverse base-change comparison preserves its explicitly supplied `R`-projection. -/
def kernelPairToArrowBaseChange_fstIso (P : Presentation X) (g : X' ⟶ X) :
    P.kernelPairToArrowBaseChange g ≫ P.arrowProjectionToGroupoid g ≅
      AlgebraicGeometry.Groupoids.arrowProjection P.atlas g ≫ P.atlasKernelToGroupoidArrow :=
  PseudoPullbackCone.lift.fstIso (P.kernelPairAsArrowBaseChangeCone g)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} P.arrowToX g)

/-- The reverse base-change comparison preserves its explicitly supplied `X'`-projection. -/
def kernelPairToArrowBaseChange_sndIso (P : Presentation X) (g : X' ⟶ X) :
    P.kernelPairToArrowBaseChange g ≫
        TwoFibreProduct.snd.{u + 1, u, u + 1, u} P.arrowToX g ≅
      (P.kernelPairAsAtlasKernelBaseChangeCone g).snd :=
  PseudoPullbackCone.lift.sndIso (P.kernelPairAsArrowBaseChangeCone g)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} P.arrowToX g)

/-- Inverse law for the named comparisons identifying `R ×_X X'` with `U' ×_{X'} U'`. -/
theorem arrowBaseChangeToKernelPair_comp_kernelPairToArrowBaseChange
    (P : Presentation X) (g : X' ⟶ X) :
    Nonempty (P.arrowBaseChangeToKernelPair g ≫ P.kernelPairToArrowBaseChange g ≅
      𝟙 (P.arrowBaseChange g)) :=
  sorry

/-- Reverse inverse law for the named comparisons identifying `R ×_X X'` with
`U' ×_{X'} U'`. -/
theorem kernelPairToArrowBaseChange_comp_arrowBaseChangeToKernelPair
    (P : Presentation X) (g : X' ⟶ X) :
    Nonempty (P.kernelPairToArrowBaseChange g ≫ P.arrowBaseChangeToKernelPair g ≅
      𝟙 (kernelPair (P.pullbackAtlas g))) :=
  sorry

/-- The arrow of `pr` on the kernel-pair representative is the actual first projection
`R ×_X X' ⟶ R`, transported along the explicit reverse base-change comparison. -/
def kernelPairToGroupoidArrow (P : Presentation X) (g : X' ⟶ X) :
    kernelPair (P.pullbackAtlas g) ⟶ P.groupoid.R.left.toGroupoids :=
  P.kernelPairToArrowBaseChange g ≫ P.arrowProjectionToGroupoid g

/-- `kernelPairToGroupoidArrow` is the actual base-change projection after the reverse comparison. -/
theorem kernelPairToGroupoidArrow_eq (P : Presentation X) (g : X' ⟶ X) :
    P.kernelPairToGroupoidArrow g =
      P.kernelPairToArrowBaseChange g ≫ P.arrowProjectionToGroupoid g :=
  sorry

/-- `kernelPairToGroupoidArrow` is 2-isomorphic to `arrowProjection` followed by the recovered
`R`-arrow, as the first-projection comparison of `kernelPairToArrowBaseChange`. -/
def kernelPairToGroupoidArrow_iso_arrowProjection (P : Presentation X) (g : X' ⟶ X) :
    P.kernelPairToGroupoidArrow g ≅
      AlgebraicGeometry.Groupoids.arrowProjection P.atlas g ≫ P.atlasKernelToGroupoidArrow :=
  P.kernelPairToArrowBaseChange_fstIso g

/-- The arrow component of `pr`, recovered from `pr_R` transported to the kernel-pair
representative of the pulled-back atlas. -/
def pullbackPr_arrow (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g) :
    (P.pullbackGroupoid g hg).R ⟶ P.groupoid.R :=
  overRecover (representingEquiv (P.pullbackKernel_isRepresentable g hg))
    (Bicategory.Equivalence.id _) (P.kernelPairToGroupoidArrow g)

/-- `pullbackPr_arrow` is recovered from `kernelPairToGroupoidArrow`. -/
theorem pullbackPr_arrow_eq (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g) :
    P.pullbackPr_arrow g hg =
      overRecover (representingEquiv (P.pullbackKernel_isRepresentable g hg))
        (Bicategory.Equivalence.id _) (P.kernelPairToGroupoidArrow g) :=
  sorry

/-- Associativity: transporting `pr_R` through `(U ×_X U) ×_X X'` recovers
`kernelPairToGroupoidArrow`, as the first-projection comparison of the associativity lift
followed by the recovered `R`-arrow. -/
def kernelPairToGroupoidArrow_associativity (P : Presentation X) (g : X' ⟶ X) :
    P.kernelPairToAtlasKernelBaseChange g ≫
        TwoFibreProduct.fst.{u + 1, u, u + 1, u} P.atlasKernelToX g ≫
          P.atlasKernelToGroupoidArrow ≅
      P.kernelPairToGroupoidArrow g :=
  (α_ (P.kernelPairToAtlasKernelBaseChange g)
      (TwoFibreProduct.fst.{u + 1, u, u + 1, u} P.atlasKernelToX g)
      P.atlasKernelToGroupoidArrow).symm ≪≫
    whiskerRightIso (P.kernelPairToAtlasKernelBaseChange_fstIso g)
      P.atlasKernelToGroupoidArrow ≪≫
    (P.kernelPairToArrowBaseChange_fstIso g).symm

/-- Transporting the recovered projection back along the forward comparison is 2-isomorphic
to the original first projection `R ×_X X' ⟶ R`, by whiskering the round-trip inverse law. -/
theorem arrowBaseChangeToKernelPair_comp_kernelPairToGroupoidArrow
    (P : Presentation X) (g : X' ⟶ X) :
    Nonempty
      (P.arrowBaseChangeToKernelPair g ≫ P.kernelPairToGroupoidArrow g ≅
        P.arrowProjectionToGroupoid g) :=
  sorry

/-- The morphism of groupoids `pr : (U', R', s', t', c') ⟶ (U, R, s, t, c)` induced by the
projections `U' ⟶ U` and `R' ⟶ R`. -/
def pullbackPr (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g) :
    Hom (P.pullbackGroupoid g hg) P.groupoid where
  obj := P.pullbackPr_obj g hg
  arrow := P.pullbackPr_arrow g hg
  map_s := sorry
  map_t := sorry
  map_c := sorry

/-- The object map of `pullbackPr` is `pullbackPr_obj`. -/
theorem pullbackPr_obj_spec (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g) :
    (P.pullbackPr g hg).obj = P.pullbackPr_obj g hg :=
  sorry

/-- The arrow map of `pullbackPr` is `pullbackPr_arrow`. -/
theorem pullbackPr_arrow_spec (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g) :
    (P.pullbackPr g hg).arrow = P.pullbackPr_arrow g hg :=
  sorry

/-- The quotient stack of the presenting groupoid is a stack on the big fppf site. -/
instance instIsStackOnSite_groupoid_quotientStack (P : Presentation X) :
    IsStack.OnSite (Scheme.fppfTopology.over S) P.groupoid.quotientStack.p :=
  IsStack.InGroupoids.toOnSite inferInstance

/-- The functor of Chap94 groupoid-valued points induced by `pullbackPr`. -/
def pullbackPr_presheafMap (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g) :
    (P.pullbackGroupoid g hg).groupoidPresheaf ⟶ P.groupoid.groupoidPresheaf where
  app T :=
    { obj := fun x ↦ (P.pullbackPr g hg).obj.left.app T x
      map := fun p ↦
        FunctorPointHom.ofArrow ((P.pullbackPr g hg).arrow.left.app T p.arrow) sorry sorry
      map_id := sorry
      map_comp := sorry }
  naturality := sorry

/-- Naturality of `pullbackPr_presheafMap` after composing with `Grpd.forgetToCat`. -/
theorem pullbackPr_presheafForget_naturality (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g) {a b}
    (f : a ⟶ b) :
    ((P.pullbackGroupoid g hg).groupoidPresheaf ⋙ Grpd.forgetToCat).toPseudofunctor'.map f ≫
        Grpd.forgetToCat.map ((P.pullbackPr_presheafMap g hg).app b.as) =
      Grpd.forgetToCat.map ((P.pullbackPr_presheafMap g hg).app a.as) ≫
        (P.groupoid.groupoidPresheaf ⋙ Grpd.forgetToCat).toPseudofunctor'.map f :=
  sorry

/-- The naturality isomorphism of `pullbackPr_presheafStrongTrans`, with forward and reverse
cells the canonical transports of `pullbackPr_presheafForget_naturality`; only the inverse
laws are deferred. -/
def pullbackPr_presheafStrongTrans_naturality (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g) {a b}
    (f : a ⟶ b) :
    ((P.pullbackGroupoid g hg).groupoidPresheaf ⋙ Grpd.forgetToCat).toPseudofunctor'.map f ≫
        Grpd.forgetToCat.map ((P.pullbackPr_presheafMap g hg).app b.as) ≅
      Grpd.forgetToCat.map ((P.pullbackPr_presheafMap g hg).app a.as) ≫
        (P.groupoid.groupoidPresheaf ⋙ Grpd.forgetToCat).toPseudofunctor'.map f where
  hom := eqToHom (P.pullbackPr_presheafForget_naturality g hg f)
  inv := eqToHom (P.pullbackPr_presheafForget_naturality g hg f).symm
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The strong transformation of co-Grothendieck pseudofunctors associated to
`pullbackPr_presheafMap`. -/
def pullbackPr_presheafStrongTrans (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g) :
    ((P.pullbackGroupoid g hg).groupoidPresheaf ⋙ Grpd.forgetToCat).toPseudofunctor' ⟶
      (P.groupoid.groupoidPresheaf ⋙ Grpd.forgetToCat).toPseudofunctor' where
  app T := Grpd.forgetToCat.map ((P.pullbackPr_presheafMap g hg).app T.as)
  naturality := P.pullbackPr_presheafStrongTrans_naturality g hg
  naturality_naturality := sorry
  naturality_id := sorry
  naturality_comp := sorry

/-- The total functor of co-Grothendieck projections induced by `pullbackPr`. -/
def pullbackPreQuotientMapFunctor (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g) :
    (P.pullbackGroupoid g hg).preQuotient.total ⥤ P.groupoid.preQuotient.total :=
  Pseudofunctor.CoGrothendieck.map (P.pullbackPr_presheafStrongTrans g hg)

/-- The prestack map `[U' /ₚ R'] ⟶ [U /ₚ R]` induced by `pullbackPr`. -/
def pullbackPreQuotientMap (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g) :
    (P.pullbackGroupoid g hg).preQuotient ⟶ P.groupoid.preQuotient :=
  ofBasedFunctor (BasedFunctor.ofFunctor (P.pullbackPreQuotientMapFunctor g hg) sorry)

/-- The cartesian based functor underlying `pullbackPreQuotientMap`. -/
def pullbackPreQuotientMapCartesian (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g) :
    CartesianBasedFunctor (P.pullbackGroupoid g hg).preQuotient.p P.groupoid.preQuotient.p :=
  CartesianBasedFunctor.ofTargetInGroupoids
    (BasedFunctor.ofFunctor (P.pullbackPreQuotientMapFunctor g hg) sorry)

/-- The composite `[U' /ₚ R'] ⟶ [U / R]` of the prestack map of `pr` with stackification of
the target. -/
def pullbackPreQuotientToQuotient (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g) :
    CartesianBasedFunctor (P.pullbackGroupoid g hg).preQuotient.p P.groupoid.quotientStack.p :=
  (P.pullbackPreQuotientMapCartesian g hg).comp P.groupoid.stackificationPresentation.comparison

/-- The selected stackification lift of `pullbackPreQuotientToQuotient` through
`[U' /ₚ R'] ⟶ [U' / R']`. -/
def pullbackQuotientLift (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g) :
    CartesianBasedFunctor.IsStackification.LiftChoice
      (i := (P.pullbackGroupoid g hg).stackificationPresentation.comparison)
      (P.pullbackPreQuotientToQuotient g hg) :=
  CartesianBasedFunctor.IsStackification.liftChoice
    (P.pullbackGroupoid g hg).stackificationPresentation.isStackification
    (P.pullbackPreQuotientToQuotient g hg)

/-- The actual comparison carried by the selected Chap94 stackification lift. -/
def pullbackQuotientLift_comparison (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g) :
    (CartesianBasedFunctor.precomp P.groupoid.quotientStack.p
        (P.pullbackGroupoid g hg).stackificationPresentation.comparison).obj
      (P.pullbackQuotientLift g hg).lift ≅ P.pullbackPreQuotientToQuotient g hg :=
  (P.pullbackQuotientLift g hg).comparison

/-- The morphism `[pr] : [U' / R'] ⟶ [U / R]` of Chap94 quotient stacks, as the stackification
lift of the prestack map induced by `pullbackPr`. -/
def pullbackQuotientMap (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g) :
    (P.pullback g hg).groupoid.quotientStack ⟶ P.groupoid.quotientStack :=
  ofBasedFunctor (CartesianBasedFunctor.toBasedFunctor (P.pullbackQuotientLift g hg).lift)

/-- `pullbackQuotientMap` is the groupoid-fibred morphism associated to the selected
stackification lift of `pullbackPreQuotientToQuotient`. -/
theorem pullbackQuotientMap_eq (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g) :
    toBasedFunctor (P.pullbackQuotientMap g hg) =
      CartesianBasedFunctor.toBasedFunctor (P.pullbackQuotientLift g hg).lift :=
  sorry

/-- `[pr]` is the stackification lift of the prestack map induced by `pullbackPr`: this is
`pullbackQuotientLift_comparison` as a `2`-isomorphism of groupoid fibrations. -/
def pullbackQuotientMap_isLift (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g) :
    (P.pullbackGroupoid g hg).stackificationHom ≫ P.pullbackQuotientMap g hg ≅
      P.pullbackPreQuotientMap g hg ≫ P.groupoid.stackificationHom :=
  BasedFunctorIso.lift
    (CartesianBasedFunctor.toBasedIso (P.pullbackQuotientLift_comparison g hg))

/-- The `fCan` comparison of the pulled-back atlas, as a `2`-isomorphism of groupoid
fibrations. -/
def pullback_fCan_comparison (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g) :
    (P.pullback g hg).groupoid.stackificationHom ≫ (P.pullback g hg).hom ≅
      AlgebraicStack.fPre (P.pullbackAtlas g) (P.pullbackObject_isRepresentable g hg) :=
  BasedFunctorIso.lift
    (CartesianBasedFunctor.toBasedIso
      (AlgebraicStack.fCanLift_comparison (P.pullbackAtlas g)
        (P.pullbackObject_isRepresentable g hg)))

/-- The comparison from the representing object space of the pulled-back groupoid to the
2-fibre product `U' = U ×_X X'`. -/
def pullbackRepresentingToObject (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g) :
    (P.pullbackGroupoid g hg).U.left.toGroupoids ⟶ P.pullbackObject g :=
  toGroupoids.map
      (extendBaseIdHom (representingSpace (P.pullbackObject_isRepresentable g hg))) ≫
    (representingEquiv (P.pullbackObject_isRepresentable g hg)).inv

/-- The projection `pr_U` transported to the representing object space of the pulled-back
groupoid. -/
def pullbackObjectProjection (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g) :
    (P.pullbackGroupoid g hg).U.left.toGroupoids ⟶ P.groupoid.U.left.toGroupoids :=
  P.pullbackRepresentingToObject g hg ≫ P.objectProjection g

/-- The pulled-back atlas transported to the representing object space of the pulled-back
groupoid. -/
def pullbackAtlasFromGroupoid (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g) :
    (P.pullbackGroupoid g hg).U.left.toGroupoids ⟶ X' :=
  P.pullbackRepresentingToObject g hg ≫ P.pullbackAtlas g

/-- The pulled-back prestack atlas followed by `fPre` of `U' ⟶ X'` is `2`-isomorphic to the
quotient atlas followed by `fCan`. -/
def atlasToPreQuotient_comp_fPre (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g) :
    (P.pullbackGroupoid g hg).atlasToPreQuotient ≫
        AlgebraicStack.fPre (P.pullbackAtlas g) (P.pullbackObject_isRepresentable g hg) ≅
      (P.pullback g hg).groupoid.atlas ≫ (P.pullback g hg).hom :=
  whiskerLeftIso ((P.pullbackGroupoid g hg).atlasToPreQuotient)
      (P.pullback_fCan_comparison g hg).symm ≪≫
    (α_ ((P.pullbackGroupoid g hg).atlasToPreQuotient)
      ((P.pullback g hg).groupoid.stackificationHom) ((P.pullback g hg).hom)).symm

/-- `comparisonIso` of the atlas square, transported to the representing object space of the
pulled-back groupoid. -/
def pullbackObjectProjection_comp_atlas (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g) :
    P.pullbackObjectProjection g hg ≫ P.atlas ≅ P.pullbackAtlasFromGroupoid g hg ≫ g :=
  (α_ (P.pullbackRepresentingToObject g hg) (P.objectProjection g) P.atlas).symm ≪≫
    whiskerLeftIso (P.pullbackRepresentingToObject g hg)
      (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} P.atlas g) ≪≫
    α_ (P.pullbackRepresentingToObject g hg) (P.pullbackAtlas g) g

/-- The point of `U' = U ×_X X'` associated to a co-Grothendieck object of `[U' /ₚ R']`. -/
def pullbackPreQuotient_apexPoint (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g)
    (x : (P.pullbackGroupoid g hg).preQuotient.total) :
    (P.pullbackObject g).total :=
  (presentedPointToU (P.pullbackAtlas g) (P.pullbackObject_isRepresentable g hg)
      (coGrothendieckPoint (P.pullbackAtlas g) (P.pullbackObject_isRepresentable g hg) x)).1

/-- Objectwise atlas comparison `pr_U ≫ atlas ≅ pullbackAtlas ≫ g` at a point of `U'`. -/
def pullbackAtlasComparison_app (P : Presentation X) (g : X' ⟶ X)
    (u' : (P.pullbackObject g).total) :
    (toFunctor (P.objectProjection g ≫ P.atlas)).obj u' ≅
      (toFunctor (P.pullbackAtlas g ≫ g)).obj u' :=
  (BasedNatIso.toNatIso
      (FiberedCategoryOver.Groupoids.toBasedFunctorIso
        (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} P.atlas g))).app u'

/-- On objects, `pr_pre ≫ i ≫ P.hom` recovers `pr_U ≫ atlas` at the associated apex point. -/
theorem pullbackPreQuotientMap_comp_presentationHom_obj_fst
    (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g)
    (x : (P.pullbackGroupoid g hg).preQuotient.total) :
    (toFunctor
        (P.pullbackPreQuotientMap g hg ≫ P.groupoid.stackificationHom ≫ P.hom)).obj x =
      (toFunctor (P.objectProjection g ≫ P.atlas)).obj
        (P.pullbackPreQuotient_apexPoint g hg x) :=
  sorry

/-- On objects, `fPre' ≫ g` recovers `pullbackAtlas ≫ g` at the associated apex point. -/
theorem pullbackPreQuotientMap_comp_presentationHom_obj_snd
    (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g)
    (x : (P.pullbackGroupoid g hg).preQuotient.total) :
    (toFunctor
        (AlgebraicStack.fPre (P.pullbackAtlas g)
          (P.pullbackObject_isRepresentable g hg) ≫ g)).obj x =
      (toFunctor (P.pullbackAtlas g ≫ g)).obj
        (P.pullbackPreQuotient_apexPoint g hg x) :=
  sorry

/-- Component of the prestack functoriality cell of `pr` at a co-Grothendieck point: the atlas
`comparisonIso` at the associated point of `U' = U ×_X X'`, conjugated by the object
identifications of `pr_pre ≫ i ≫ P.hom` and `fPre' ≫ g`. -/
def pullbackPreQuotientMap_comp_presentationHom_app (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g)
    (x : (P.pullbackGroupoid g hg).preQuotient.total) :
    (toFunctor
        (P.pullbackPreQuotientMap g hg ≫ P.groupoid.stackificationHom ≫ P.hom)).obj x ≅
      (toFunctor
        (AlgebraicStack.fPre (P.pullbackAtlas g)
          (P.pullbackObject_isRepresentable g hg) ≫ g)).obj x :=
  eqToIso (P.pullbackPreQuotientMap_comp_presentationHom_obj_fst g hg x) ≪≫
    P.pullbackAtlasComparison_app g (P.pullbackPreQuotient_apexPoint g hg x) ≪≫
    (eqToIso (P.pullbackPreQuotientMap_comp_presentationHom_obj_snd g hg x)).symm

/-- The exact kernel-pair compatibility of 04Y7 needed for prestack arrow naturality. -/
abbrev pullbackSquareKernelCoherence (P : Presentation X) (g : X' ⟶ X) : Prop :=
  let psi := AlgebraicGeometry.Groupoids.selfFibreCospan P.atlas g
  let f' := P.pullbackAtlas g
  TwoFibreProduct.map.comparisonIso psi =
    whiskerRightIso (TwoFibreProduct.map.fstIso psi) P.atlas ≪≫
      α_ (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f' f') psi.left P.atlas ≪≫
      whiskerLeftIso (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f' f') psi.leftIso ≪≫
      (α_ (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f' f') f' psi.base).symm ≪≫
      whiskerRightIso (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} f' f') psi.base ≪≫
      α_ (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f' f') f' psi.base ≪≫
      whiskerLeftIso (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f' f') psi.rightIso.symm ≪≫
      (α_ (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f' f') psi.right P.atlas).symm ≪≫
      whiskerRightIso (TwoFibreProduct.map.sndIso psi).symm P.atlas

/-- The given prestack components are natural when the source/target comparison cells
agree. The fibre-arrow case uses 04Y7 and `fPreTotal`'s canonical-arrow formula. -/
theorem pullbackPreQuotientMap_comp_presentationHom_naturality
    (P : Presentation X) (g : X' ⟶ X) (hg : relativelyRepresentableByAlgebraicSpaces g)
    (hτ : P.pullbackSquareKernelCoherence g)
    {a b : (P.pullbackGroupoid g hg).preQuotient.total} (φ : a ⟶ b) :
    (toFunctor (P.pullbackPreQuotientMap g hg ≫ P.groupoid.stackificationHom ≫ P.hom)).map φ ≫
        (P.pullbackPreQuotientMap_comp_presentationHom_app g hg b).hom =
      (P.pullbackPreQuotientMap_comp_presentationHom_app g hg a).hom ≫
        (toFunctor (AlgebraicStack.fPre (P.pullbackAtlas g)
          (P.pullbackObject_isRepresentable g hg) ≫ g)).map φ := sorry

/-- Functoriality of the prestack maps of `pr` and of the pulled-back atlas. The atlas-level
cell is `TwoFibreProduct.comparisonIso P.atlas g`; equation 04Y7 is
`Groupoids.selfComparison_whisker_eq P.atlas g`. -/
def pullbackPreQuotientMap_comp_presentationHom (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g) :
    P.pullbackPreQuotientMap g hg ≫ P.groupoid.stackificationHom ≫ P.hom ≅
      AlgebraicStack.fPre (P.pullbackAtlas g) (P.pullbackObject_isRepresentable g hg) ≫ g :=
  BasedFunctorIso.lift
    (ofComponents (P.pullbackPreQuotientMap_comp_presentationHom_app g hg)
      (P.pullbackPreQuotientMap_comp_presentationHom_naturality g hg
        (AlgebraicGeometry.Groupoids.selfComparison_whisker_eq P.atlas g))
      (fun _ ↦ sorry))

/-- Precomposition with stackification of `[U' /ₚ R']` is an equivalence on morphisms into the
algebraic stack `X`. -/
instance instIsEquivalence_pullbackStackification_precomp
    (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g) :
    (Bicategory.precomp X
        ((P.pullback g hg).groupoid.stackificationHom)).IsEquivalence :=
  sorry

/-- The Hom-equivalence on morphisms into `X` induced by stackification of `[U' /ₚ R']`. -/
def pullbackStackification_homEquivalence (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g) :
    ((P.pullback g hg).groupoid.quotientStack ⟶ X) ≌
      ((P.pullback g hg).groupoid.preQuotient ⟶ X) :=
  Functor.asEquivalence
    (Bicategory.precomp X ((P.pullback g hg).groupoid.stackificationHom))

/-- Precomposition of the two square composites with stackification of `[U' /ₚ R']`. The
forward cell uses `pullbackQuotientMap_isLift`, the `fCan` comparison, associators, whiskering,
`TwoFibreProduct.comparisonIso P.atlas g`, and `Groupoids.selfComparison_whisker_eq P.atlas g`. -/
def pullbackSquareIso_precomp (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g) :
    (P.pullback g hg).groupoid.stackificationHom ≫ P.pullbackQuotientMap g hg ≫ P.hom ≅
      (P.pullback g hg).groupoid.stackificationHom ≫ (P.pullback g hg).hom ≫ g :=
  (α_ ((P.pullback g hg).groupoid.stackificationHom)
      (P.pullbackQuotientMap g hg) P.hom).symm ≪≫
    whiskerRightIso (P.pullbackQuotientMap_isLift g hg) P.hom ≪≫
    α_ (P.pullbackPreQuotientMap g hg) P.groupoid.stackificationHom P.hom ≪≫
    P.pullbackPreQuotientMap_comp_presentationHom g hg ≪≫
    (whiskerRightIso (P.pullback_fCan_comparison g hg) g).symm ≪≫
    α_ ((P.pullback g hg).groupoid.stackificationHom) ((P.pullback g hg).hom) g

/-- The square with left leg `[pr]`, top the pulled-back presentation, right leg `g`, and
bottom the given presentation map `P.hom` is `2`-commutative. The filling `2`-cell is the
unique descent of `pullbackSquareIso_precomp` along stackification of `[U' /ₚ R']`. -/
def pullbackSquareIso (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g) :
    P.pullbackQuotientMap g hg ≫ P.hom ≅ (P.pullback g hg).hom ≫ g :=
  (P.pullbackStackification_homEquivalence g hg).fullyFaithfulFunctor.preimageIso
    (P.pullbackSquareIso_precomp g hg)

/-- The actual forward descended cell recovers the specified composite after precomposition. -/
theorem pullbackSquareIso_hom_spec (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g) :
    (Bicategory.precomp X (P.pullbackGroupoid g hg).stackificationHom).map
        (P.pullbackSquareIso g hg).hom = (P.pullbackSquareIso_precomp g hg).hom :=
  (P.pullbackStackification_homEquivalence g hg).fullyFaithfulFunctor.map_preimage _

/-- The actual inverse descended cell recovers the inverse specified composite. -/
theorem pullbackSquareIso_inv_spec (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g) :
    (Bicategory.precomp X (P.pullbackGroupoid g hg).stackificationHom).map
        (P.pullbackSquareIso g hg).inv = (P.pullbackSquareIso_precomp g hg).inv :=
  (P.pullbackStackification_homEquivalence g hg).fullyFaithfulFunctor.map_preimage _

/-- The forward cell is uniquely determined by its actual precomposition image. -/
theorem pullbackSquareIso_hom_unique (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g)
    (β : P.pullbackQuotientMap g hg ≫ P.hom ⟶ (P.pullback g hg).hom ≫ g)
    (hβ : (Bicategory.precomp X (P.pullbackGroupoid g hg).stackificationHom).map β =
      (P.pullbackSquareIso_precomp g hg).hom) : β = (P.pullbackSquareIso g hg).hom :=
  (P.pullbackStackification_homEquivalence g hg).fullyFaithfulFunctor.map_injective
    (hβ.trans (P.pullbackSquareIso_hom_spec g hg).symm)

/-- `pullbackSquareIso` is a `2`-isomorphism of the two composites of the presentation square. -/
theorem pullback_twoCommutes (P : Presentation X) (g : X' ⟶ X)
    (hg : relativelyRepresentableByAlgebraicSpaces g) :
    (P.pullbackSquareIso g hg).hom ≫ (P.pullbackSquareIso g hg).inv =
      𝟙 (P.pullbackQuotientMap g hg ≫ P.hom) :=
  (P.pullbackSquareIso g hg).hom_inv_id

end Presentation

end AlgebraicGeometry.AlgebraicStack
