/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap97.Definition_97_8_1_Algebraic
public import stacks_project.Chap97.Lemma_97_7_1_SurjectiveOnObjects
public import stacks_project.Chap99.Lemma_99_14_6_Apex
public import stacks_project.Chap99.Remark_99_15_13_Pullback
public import stacks_project.Chap100.Definition_100_9_1_Immersion
public import stacks_project.Chap101.Lemma_101_16_1_Presentation
public import stacks_project.Chap108.Lemma_108_4_3_Existence
public import stacks_project.Chap108.Lemma_108_8_5_Smooth
public import stacks_project.Chap109.Lemma_109_4_1_Groupoids

/-!
# Remark 99.15.13

The 2-fibre product Curves ×_{Spaces'_{fp, flat, proper}} Polarized parametrizes
polarized curves. The left vertical arrow PolarizedCurves ⟶ Curves is algebraic,
smooth, and surjective; PolarizedCurves is an open-and-closed substack of
Polarized; a stack in groupoids targeted by a smooth algebraic surjective
morphism from an algebraic stack is algebraic.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces hiding p
open AlgebraicGeometry.GroupScheme
open CategoryTheory.Limits
open CategoricalPullback
open FiberedCategoryOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.PolarizedCurves

/-- Remark 99.15.13 (1): the square with apex PolarizedCurves over
Curves ⟶ Spaces'_{fp, flat, proper} along Polarized ⟶ Spaces'_{fp, flat, proper}
is a 2-fibre product. -/
@[stacks 0D5C, instance]
instance instSquareIsBilimit : CatCommSqOver.Resized.IsBilimit square :=
  sorry

/-- Remark 99.15.13 (2): the left vertical arrow PolarizedCurves ⟶ Curves is
algebraic, as the base change of the algebraic 1-morphism of Lemma 99.14.6. -/
@[stacks 0D5C]
theorem algebraicStack_twoFibreProduct (ξ : Curves.Obj (⊤_ Scheme.{u})) :
    AlgebraicStack
      (Polarized.twoFibreProduct ((Curves.inclusion (⊤_ Scheme.{u})).obj ξ)) :=
  sorry

/-- Remark 99.15.13 (3): the left vertical arrow PolarizedCurves ⟶ Curves is
smooth. -/
@[stacks 0D5C, instance]
instance instSmooth_toCurvesHom : CohStack.Hom.Smooth toCurvesHom :=
  sorry

/-- Remark 99.15.13 (4): the left vertical arrow PolarizedCurves ⟶ Curves is
surjective; every point is in the image. For every field `k`, morphism
`Spec k ⟶ ⊤_ Scheme`, and object of Curves over that point, some field
extension `K / k` and an object of PolarizedCurves over `Spec K` lie over it
up to 2-isomorphism. -/
@[stacks 0D5C]
theorem toCurvesHom_surjectiveOnObjects {k : Type u} [Field k]
    (σ : Spec (.of k) ⟶ ⊤_ Scheme.{u})
    (y : Classifying.slice (Over.mk σ) ⟶ Curves.toGroupoids (⊤_ Scheme.{u})) :
    ∃ (K : Type u) (_ : Field K) (τ : Spec (.of K) ⟶ ⊤_ Scheme.{u})
      (e : Spec (.of K) ⟶ Spec (.of k)) (he : e ≫ σ = τ)
      (x : Classifying.slice (Over.mk τ) ⟶ toGroupoids),
      Nonempty (x ≫ toCurvesHom ≅ Classifying.sliceHomMk e he ≫ y) :=
  sorry

/-- Remark 99.15.13 (5): PolarizedCurves is an open and closed substack of
Polarized. -/
@[stacks 0D5C]
theorem inclusionHom_isOpenAndClosedImmersion :
    Groupoids.Hom.OpenImmersion inclusionHom ∧
      Groupoids.Hom.ClosedImmersion inclusionHom :=
  sorry

end AlgebraicGeometry.PolarizedCurves

namespace AlgebraicGeometry.AlgebraicStack

/-- Remark 99.15.13 (6): a stack in groupoids which is the target of a smooth
algebraic morphism that is surjective on objects, from an algebraic stack, is
an algebraic stack. Smoothness is a surjective smooth algebraic-space
presentation, not representability by algebraic spaces. -/
@[stacks 0D5C]
theorem of_smooth_algebraic {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X]
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) Y.p]
    (F : X ⟶ Y) [Groupoids.Hom.Algebraic F]
    [Groupoids.Hom.SurjectiveOnObjects F]
    (h_smooth : ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X)
      (b : V.toGroupoids ⟶ Y) (h : U ⟶ V),
      IsSmoothSurjectivePresentation F a b h ∧ AlgebraicSpace.Smooth h) :
    AlgebraicStack Y :=
  sorry

end AlgebraicGeometry.AlgebraicStack
