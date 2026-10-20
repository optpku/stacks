module

import Mathlib.Tactic.CrossRefAttribute
-- `HasPullbacks` is public because `representableOfProduct` assumes it.
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.DiagonalBaseChange.Comparison.SourceSquare
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.DiagonalBaseChange.Diagonal
public import ReasLib.CategoryTheory.Fibered.Representable.Slice
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Equivalences.Base
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.ProductSlice.RightVertical
public import ReasLib.CategoryTheory.Functor.OverIso

/-!
# Product-slice diagonal-base-change over-base comparison

This leaf assembles the source-square and diagonal comparisons into the
canonical over-base equivalence and representability transport API.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Bicategory
open CategoryTheory.Limits CategoryTheory.Limits.CategoricalPullback
open scoped CategoricalPullback
open scoped Pseudofunctor.StrongTrans

open Limits.CategoricalPullback.ProductSlice

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Groupoids.ProductSlice

section ProductSliceSourceRightVertical

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

variable [Limits.HasBinaryProducts C]
variable {U V : C}

namespace DiagonalBaseChange.Implementation

/-- The ordinary self-pullback comparison attached to the canonical two-fibre-product cone.

Unlike `BasedCategory.PseudoPullback.Comparison.equivalence`, this begins at the total category
of `TwoFibreProduct.cone`; `PseudoPullbackComparison.target` is the owner which supplies that
bridge without identifying the two apex presentations definitionally. -/
private noncomputable def baseProjectionComparison
    (X : FiberedCategoryOver.Groupoids C) :
    (CategoryTheory.TwoFibreProduct.cone X.baseProjection X.baseProjection).pt.1.obj ⥤
      X.p ⊡ X.p :=
  PseudoPullbackComparison.target
    (CategoryTheory.TwoFibreProduct.cone X.baseProjection X.baseProjection)

/-- The comparison from the canonical two-fibre-product cone to the ordinary self-pullback is
an equivalence. -/
private theorem baseProjectionComparison.isEquivalence
    (X : FiberedCategoryOver.Groupoids C) :
    (baseProjectionComparison X).IsEquivalence := sorry

/-- The canonical equivalence from the canonical two-fibre-product cone to the self-pullback of
`X.p`.

The equivalence retains `baseProjectionComparison` as its forward functor and packages only its
proposition-level equivalence proof; it is private because the public diagonal-base-change
comparison is its sole consumer. -/
private noncomputable def baseProjectionEquivalence
    (X : FiberedCategoryOver.Groupoids C) :
    (CategoryTheory.TwoFibreProduct.cone X.baseProjection X.baseProjection).pt.1.obj ≌
      X.p ⊡ X.p :=
  (baseProjectionComparison X).asEquivalenceOf (baseProjectionComparison.isEquivalence X)

/-- The source pseudo-pullback comparison, regarded as a functor over the `U`-slice base.

The second projection is selected because the source categorical pullback is ordered as
`G' ⊡ G`; this records the direction once instead of leaving it implicit in the final assembly. -/
private noncomputable def sourcePullbackStep
    {X : FiberedCategoryOver.Groupoids C}
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X) :
    Functor.OverIso
      (FiberedCategoryOver.Groupoids.p
        (CategoryTheory.TwoFibreProduct.apex G' G))
      (π₂ (FiberedCategoryOver.Groupoids.toFunctor G')
        (FiberedCategoryOver.Groupoids.toFunctor G) ⋙ Over.forget U) :=
  Functor.OverIso.mk
    (BasedCategory.PseudoPullback.Comparison.equivalence
      (FiberedCategoryOver.Groupoids.toBasedFunctor G')
      (FiberedCategoryOver.Groupoids.toBasedFunctor G)).functor
    (Functor.isoWhiskerLeft
        (BasedCategory.PseudoPullback.Comparison.equivalence
          (FiberedCategoryOver.Groupoids.toBasedFunctor G')
          (FiberedCategoryOver.Groupoids.toBasedFunctor G)).functor
        (Functor.isoWhiskerLeft
          (π₂ (FiberedCategoryOver.Groupoids.toFunctor G')
            (FiberedCategoryOver.Groupoids.toFunctor G))
          (eqToIso
            (FiberedCategoryOver.Groupoids.ofFunctor.p (Over.forget U))).symm) ≪≫
      BasedCategory.PseudoPullback.Comparison.sndBaseIso
        (FiberedCategoryOver.Groupoids.toBasedFunctor G')
        (FiberedCategoryOver.Groupoids.toBasedFunctor G))

/-- Transport the product-slice right vertical and diagonal along their two canonical
pseudo-pullback comparison isomorphisms, retaining the first projection over the product slice. -/
private noncomputable def legChangeStep
    {X : FiberedCategoryOver.Groupoids C}
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X) :
    Functor.OverIso
      (π₁ (sourceSquare.rightVertical (X := X) G G') (Δₚ X.p) ⋙
        Over.forget (Limits.prod U V))
      (π₁
          (FiberedCategoryOver.Groupoids.toFunctor
              (PseudoPullbackCone.map (sourceSquare.coneComparison G G')) ⋙
            (baseProjectionEquivalence X).functor)
          (FiberedCategoryOver.Groupoids.toFunctor
              (FiberedCategoryOver.Groupoids.diagonal X) ⋙
            (baseProjectionEquivalence X).functor) ⋙
        Over.forget (Limits.prod U V)) :=
  Functor.OverIso.mk
    (CategoricalPullback.LegChange.equivalence
      (sourceSquare.comparisonIso (X := X) G G')
      (Diagonal.toCategoricalPullbackIso X)).inverse
    (Functor.isoWhiskerRight
      (CategoricalPullback.LegChange.equivalence.inverseFstIso
        (sourceSquare.comparisonIso (X := X) G G')
        (Diagonal.toCategoricalPullbackIso X))
      (Over.forget (Limits.prod U V)))

/-- Undo common-base transport after the two cone comparisons, retaining the first projection
over the product slice. -/
private noncomputable def baseTransportStep
    {X : FiberedCategoryOver.Groupoids C}
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X) :
    Functor.OverIso
      (π₁
          (FiberedCategoryOver.Groupoids.toFunctor
              (PseudoPullbackCone.map (sourceSquare.coneComparison G G')) ⋙
            (baseProjectionEquivalence X).functor)
          (FiberedCategoryOver.Groupoids.toFunctor
              (FiberedCategoryOver.Groupoids.diagonal X) ⋙
            (baseProjectionEquivalence X).functor) ⋙
        Over.forget (Limits.prod U V))
      (π₁ (FiberedCategoryOver.Groupoids.toFunctor
            (PseudoPullbackCone.map (sourceSquare.coneComparison G G')))
        (FiberedCategoryOver.Groupoids.toFunctor
          (FiberedCategoryOver.Groupoids.diagonal X)) ⋙
        Over.forget (Limits.prod U V)) :=
  Functor.OverIso.mk
    (CategoricalPullback.BaseChange.equivalence
      (FiberedCategoryOver.Groupoids.toFunctor
        (PseudoPullbackCone.map (sourceSquare.coneComparison G G')))
      (FiberedCategoryOver.Groupoids.toFunctor
        (FiberedCategoryOver.Groupoids.diagonal X))
      (baseProjectionEquivalence X)).inverse
    (Functor.isoWhiskerRight
      (CategoricalPullback.BaseChange.equivalence.inverseFstIso
        (FiberedCategoryOver.Groupoids.toFunctor
          (PseudoPullbackCone.map (sourceSquare.coneComparison G G')))
        (FiberedCategoryOver.Groupoids.toFunctor
          (FiberedCategoryOver.Groupoids.diagonal X))
        (baseProjectionEquivalence X))
      (Over.forget (Limits.prod U V)))

/-- The target pseudo-pullback comparison, regarded over the product-slice base supplied by
the source square. -/
private noncomputable def targetPullbackStep
    {X : FiberedCategoryOver.Groupoids C}
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X) :
    Functor.OverIso
      (π₁ (FiberedCategoryOver.Groupoids.toFunctor
            (PseudoPullbackCone.map (sourceSquare.coneComparison G G')))
        (FiberedCategoryOver.Groupoids.toFunctor
          (FiberedCategoryOver.Groupoids.diagonal X)) ⋙
        Over.forget (Limits.prod U V))
      (FiberedCategoryOver.Groupoids.p
        (CategoryTheory.TwoFibreProduct.apex
          (PseudoPullbackCone.map (sourceSquare.coneComparison G G'))
          (FiberedCategoryOver.Groupoids.diagonal X))) :=
  Functor.OverIso.mk
    (BasedCategory.PseudoPullback.Comparison.equivalence
      (FiberedCategoryOver.Groupoids.toBasedFunctor
        (PseudoPullbackCone.map (sourceSquare.coneComparison G G')))
      (FiberedCategoryOver.Groupoids.toBasedFunctor
        (FiberedCategoryOver.Groupoids.diagonal X))).inverse
    (sourceSquare.inverseLeftBaseIso (X := X) G G'
      (PseudoPullbackCone.map (sourceSquare.coneComparison G G'))
      (FiberedCategoryOver.Groupoids.diagonal X))

end DiagonalBaseChange.Implementation

/-- The canonical comparison from a product of slice morphisms to its diagonal base change,
together with the composite natural isomorphism over `C`.

The owner composes the source pseudo-pullback comparison, the product-slice diagonal comparison,
inverse leg and base congruences, and the inverse target pseudo-pullback comparison. Keeping their
base compatibilities in one `Functor.OverIso` lets representability transport use the comparison
without reconstructing the five intermediate projection isomorphisms. -/
@[stacks 04SF "diagonal base-change comparison over the product slice"]
noncomputable def DiagonalBaseChange.comparisonOverBase
    {X : FiberedCategoryOver.Groupoids C}
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X) :
    Functor.OverIso
      (FiberedCategoryOver.Groupoids.p
        (CategoryTheory.TwoFibreProduct.apex G' G))
      (FiberedCategoryOver.Groupoids.p
        (CategoryTheory.TwoFibreProduct.apex
          (PseudoPullbackCone.map (sourceSquare.coneComparison G G'))
          (FiberedCategoryOver.Groupoids.diagonal X))) :=
  (DiagonalBaseChange.Implementation.sourcePullbackStep (X := X) G G').comp
    ((Diagonal.comparisonOverBase
        (FiberedCategoryOver.Groupoids.commIso G)
        (FiberedCategoryOver.Groupoids.commIso G')).comp
      ((DiagonalBaseChange.Implementation.legChangeStep (X := X) G G').comp
        ((DiagonalBaseChange.Implementation.baseTransportStep (X := X) G G').comp
          (DiagonalBaseChange.Implementation.targetPullbackStep (X := X) G G'))))

/-- The underlying functor of the diagonal-base-change over-base comparison is an
equivalence. -/
instance DiagonalBaseChange.comparisonOverBase.isEquivalence
    {X : FiberedCategoryOver.Groupoids C}
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X) :
    (DiagonalBaseChange.comparisonOverBase (X := X) G G').functor.IsEquivalence := sorry
/- Proof strategy: unfold `DiagonalBaseChange.comparisonOverBase`; each of the five over-base
steps has an equivalence as its underlying functor, and
`Functor.OverIso.compFunctorIsEquivalence` combines them. -/

/-- The total-category equivalence comparing a product of slice morphisms with diagonal base
change, derived from the canonical over-base comparison. -/
@[stacks 04SF "diagonal base-change equivalence over the product slice"]
noncomputable def DiagonalBaseChange.equivalence
    {X : FiberedCategoryOver.Groupoids C}
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X) :
    FiberedCategoryOver.Groupoids.total
        (CategoryTheory.TwoFibreProduct.apex G' G) ≌
      FiberedCategoryOver.Groupoids.total
        (CategoryTheory.TwoFibreProduct.apex
          (PseudoPullbackCone.map (sourceSquare.coneComparison G G'))
          (FiberedCategoryOver.Groupoids.diagonal X)) :=
  (DiagonalBaseChange.comparisonOverBase (X := X) G G').asEquivalence

/-- The forward functor of the diagonal-base-change equivalence is the functor retained by its
over-base owner. -/
@[simp]
theorem DiagonalBaseChange.equivalence.functor
    {X : FiberedCategoryOver.Groupoids C}
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X) :
    (DiagonalBaseChange.equivalence (X := X) G G').functor =
      (DiagonalBaseChange.comparisonOverBase (X := X) G G').functor := sorry

/-- Representability of a product of slice morphisms is equivalent to representability of the
corresponding diagonal base change. -/
theorem DiagonalBaseChange.representable.iff
    {X : FiberedCategoryOver.Groupoids C}
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X) :
    IsRepresentable (CategoryTheory.TwoFibreProduct.apex G' G) ↔
      IsRepresentable
        (CategoryTheory.TwoFibreProduct.apex
          (PseudoPullbackCone.map (sourceSquare.coneComparison G G'))
          (FiberedCategoryOver.Groupoids.diagonal X)) := sorry
/- Proof strategy: apply `FiberedCategoryOver.Groupoids.IsRepresentable.iff_ofOverIso` to
`DiagonalBaseChange.comparisonOverBase G G'`. -/

/-- Transport representability from the diagonal base change to the product-slice pullback. -/
theorem DiagonalBaseChange.representable.source
    {X : FiberedCategoryOver.Groupoids C}
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X) :
    IsRepresentable
        (CategoryTheory.TwoFibreProduct.apex
          (PseudoPullbackCone.map (sourceSquare.coneComparison G G'))
          (FiberedCategoryOver.Groupoids.diagonal X)) →
      IsRepresentable (CategoryTheory.TwoFibreProduct.apex G' G) := sorry
/- Proof strategy: use the reverse implication of
`DiagonalBaseChange.representable.iff G G'`. -/

/-- Reverse transport from the product-slice pullback to the diagonal base change. -/
theorem DiagonalBaseChange.representable.target
    {X : FiberedCategoryOver.Groupoids C}
    (G : slice U ⟶ X)
    (G' : slice V ⟶ X) :
    IsRepresentable (CategoryTheory.TwoFibreProduct.apex G' G) →
      IsRepresentable
        (CategoryTheory.TwoFibreProduct.apex
          (PseudoPullbackCone.map (sourceSquare.coneComparison G G'))
          (FiberedCategoryOver.Groupoids.diagonal X)) := sorry
/- Proof strategy: use the forward implication of
`DiagonalBaseChange.representable.iff G G'`. -/

omit [HasBinaryProducts C] in
/-- After replacing the product pullback by the product-slice/diagonal comparison, base-change
along `W ⟶ W × W`. -/
theorem DiagonalBaseChange.representable.ofProduct
    [Limits.HasBinaryProducts C] [Limits.HasPullbacks C]
    {X : FiberedCategoryOver.Groupoids C} {W : C}
    (L R : slice W ⟶ X)
    (hprodLR : IsRepresentable (CategoryTheory.TwoFibreProduct.apex R L)) :
    IsRepresentable (CategoryTheory.TwoFibreProduct.apex
      (FiberedCategoryOver.Groupoids.overMap
        (Limits.prod.lift (𝟙 W) (𝟙 W) : W ⟶ Limits.prod W W) ≫
          PseudoPullbackCone.map (sourceSquare.coneComparison L R))
      (FiberedCategoryOver.Groupoids.diagonal X)) := sorry
/- Proof strategy: first apply
`DiagonalBaseChange.representable.target`. Then base-change the resulting
representable object along `Limits.prod.lift (𝟙 W) (𝟙 W)` using
`TwoFibreProduct.IsRepresentable.ofOverMap`, and finish with
the forward direction of `TwoFibreProduct.ObjectProperty.leftProjection_iff`, specialized to
`FiberedCategoryOver.Groupoids.IsRepresentable`. -/

end ProductSliceSourceRightVertical

end FiberedCategoryOver.Groupoids.ProductSlice

end CategoryTheory
