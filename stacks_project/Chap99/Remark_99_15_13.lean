module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.PolarizedCurves.ToCurves
public import ReasLib.AlgebraicGeometry.Polarized.Algebraic
public import ReasLib.AlgebraicGeometry.PolarizedCurves.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicStack.AtlasCriterion

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

/- Remark 99.15.13 (1): the square with apex PolarizedCurves over
Curves ⟶ Spaces'_{fp, flat, proper} along Polarized ⟶ Spaces'_{fp, flat, proper}
is a 2-fibre product. -/
@[stacks 0D5C] #check
  (AlgebraicGeometry.PolarizedCurves.instSquareIsBilimit :
    CatCommSqOver.Resized.IsBilimit square)

variable (ξ : Curves.Obj (⊤_ Scheme.{u}))

/- Remark 99.15.13 (2): the left vertical arrow PolarizedCurves ⟶ Curves is
algebraic, as the base change of the algebraic 1-morphism of Lemma 99.14.6. -/
@[stacks 0D5C] #check
  (AlgebraicGeometry.Polarized.instAlgebraicStack_twoFibreProduct
    ((Curves.inclusion (⊤_ Scheme.{u})).obj ξ) :
    AlgebraicStack
      (Polarized.twoFibreProduct ((Curves.inclusion (⊤_ Scheme.{u})).obj ξ)))

/- Remark 99.15.13 (3): the left vertical arrow PolarizedCurves ⟶ Curves is
smooth. -/
@[stacks 0D5C] #check (AlgebraicGeometry.PolarizedCurves.instSmoothToCurvesHom :
  CohStack.Hom.Smooth toCurvesHom)

/- Remark 99.15.13 (4): the left vertical arrow PolarizedCurves ⟶ Curves is
surjective; every point is in the image. For every field `k`, morphism
`Spec k ⟶ ⊤_ Scheme`, and object of Curves over that point, some field
extension `K / k` and an object of PolarizedCurves over `Spec K` lie over it
up to 2-isomorphism. -/
@[stacks 0D5C] #check (AlgebraicGeometry.PolarizedCurves.toCurvesHom_surjectiveOnObjects :
  ∀ {k : Type u} [Field k]
    (σ : Spec (.of k) ⟶ ⊤_ Scheme.{u})
    (y : Classifying.slice (Over.mk σ) ⟶ Curves.toGroupoids (⊤_ Scheme.{u})),
    ∃ (K : Type u) (_ : Field K) (τ : Spec (.of K) ⟶ ⊤_ Scheme.{u})
      (e : Spec (.of K) ⟶ Spec (.of k)) (he : e ≫ σ = τ)
      (x : Classifying.slice (Over.mk τ) ⟶ toGroupoids),
      Nonempty (x ≫ toCurvesHom ≅ Classifying.sliceHomMk e he ≫ y))

/- Remark 99.15.13 (5): PolarizedCurves is an open and closed substack of
Polarized. -/
@[stacks 0D5C] #check (AlgebraicGeometry.PolarizedCurves.inclusionHom_isOpenAndClosedImmersion :
    Groupoids.Hom.OpenImmersion inclusionHom ∧
      Groupoids.Hom.ClosedImmersion inclusionHom)

end AlgebraicGeometry.PolarizedCurves

namespace AlgebraicGeometry.AlgebraicStack

/- Remark 99.15.13 (6): a stack in groupoids which is the target of a smooth
algebraic morphism that is surjective on objects, from an algebraic stack, is
an algebraic stack. Smoothness is a surjective smooth algebraic-space
presentation, not representability by algebraic spaces. -/
@[stacks 0D5C] #check (AlgebraicGeometry.AlgebraicStack.of_smooth_algebraic :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X]
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) Y.p]
    (F : X ⟶ Y) [Groupoids.Hom.Algebraic F]
    [Groupoids.Hom.SurjectiveOnObjects F]
    (h_smooth : ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X)
      (b : V.toGroupoids ⟶ Y) (h : U ⟶ V),
      IsSmoothSurjectivePresentation F a b h ∧ AlgebraicSpace.Smooth h),
    AlgebraicStack Y)

end AlgebraicGeometry.AlgebraicStack
