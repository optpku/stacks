/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Basic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.InGroupoids.PseudoPullback
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Closure
public import ReasLib.CategoryTheory.Fibered.Setoids.Bicategory
import ReasLib.CategoryTheory.Limits.CategoricalPullback.Faithful

/-!
# Pseudo-pullbacks of categories fibred in setoids

Faithfulness of the explicit based pseudo-pullback projection is inherited from its two source
projections. Together with groupoid-valued closure, this gives closure of categories fibred in
setoids under the common two-fibre-product construction. The raw statements allow independent
universes and distinguish cartesian-leg closure from its target-in-groupoids and full-property
specializations.
-/

@[expose] public section

universe u v w vB uX vX uY vY uS vS

namespace CategoryTheory

open Bicategory ObjectProperty

variable {C : Type u} [Category.{v} C]

namespace BasedCategory.PseudoPullback

variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}
variable {S : BasedCategory.{vS, uS} C}

/-- The projection of a based pseudo-pullback is faithful whenever both source projections are
faithful. -/
instance Projection.faithful
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)
    [X.p.Faithful] [Y.p.Faithful] :
    (BasedCategory.PseudoPullback F G).p.Faithful := sorry
/- Proof strategy: equality after projection identifies both component maps by faithfulness of
`X.p` and `Y.p`; conclude with `PseudoPullback.hom_ext`. -/

/-- The projection of a based pseudo-pullback is faithful when the left cospan leg and the
right source projection are faithful. This is the asymmetric form needed when only the right
source is fibred in setoids. -/
@[stacks 05UI "left-leg faithful pseudo-pullback projection"]
theorem Projection.faithfulOfLeft
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)
    (hF : F.Faithful) [Y.p.Faithful] :
    (BasedCategory.PseudoPullback F G).p.Faithful := sorry

/-- The projection of a based pseudo-pullback is faithful when the right cospan leg and the
left source projection are faithful. -/
@[stacks 05UI "right-leg faithful pseudo-pullback projection"]
theorem Projection.faithfulOfRight
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)
    (hG : G.Faithful) [X.p.Faithful] :
    (BasedCategory.PseudoPullback F G).p.Faithful := sorry

/-- The pseudo-pullback of cartesian based functors with setoid-fibred domains is again fibred in
setoids. The common target need not itself be fibred: cartesianity supplies fibredness of the
pseudo-pullback projection, while source faithfulness supplies its faithful component. -/
instance Projection.InSetoids.ofCartesian
    (F : CartesianBasedFunctor X.p S.p)
    (G : CartesianBasedFunctor Y.p S.p)
    [Functor.IsFibered.InSetoids X.p]
    [Functor.IsFibered.InSetoids Y.p] :
    Functor.IsFibered.InSetoids
      (BasedCategory.PseudoPullback
        F.toBasedFunctor G.toBasedFunctor).p := sorry
/- Proof strategy: combine `projectionIsFibered F G` with
`Projection.faithful F.toBasedFunctor G.toBasedFunctor`, then apply
`Functor.IsFibered.InSetoids.iff_inGroupoids_faithful`. -/

/-- A cartesian based pseudo-pullback is fibred in setoids when its left leg is faithful, its
left source is fibred in groupoids, and its right source is fibred in setoids. No fibredness
hypothesis is needed on the common target. -/
@[stacks 05UI "left-leg mixed setoid pseudo-pullback closure"]
theorem Projection.InSetoids.ofCartesianLeft
    (F : CartesianBasedFunctor X.p S.p)
    (G : CartesianBasedFunctor Y.p S.p)
    (hF : F.toBasedFunctor.Faithful)
    [Functor.IsFibered.InGroupoids X.p]
    [Functor.IsFibered.InSetoids Y.p] :
    Functor.IsFibered.InSetoids
      (BasedCategory.PseudoPullback
        F.toBasedFunctor G.toBasedFunctor).p := sorry

/-- A cartesian based pseudo-pullback is fibred in setoids when its right leg is faithful, its
right source is fibred in groupoids, and its left source is fibred in setoids. -/
@[stacks 05UI "right-leg mixed setoid pseudo-pullback closure"]
theorem Projection.InSetoids.ofCartesianRight
    (F : CartesianBasedFunctor X.p S.p)
    (G : CartesianBasedFunctor Y.p S.p)
    (hG : G.toBasedFunctor.Faithful)
    [Functor.IsFibered.InSetoids X.p]
    [Functor.IsFibered.InGroupoids Y.p] :
    Functor.IsFibered.InSetoids
      (BasedCategory.PseudoPullback
        F.toBasedFunctor G.toBasedFunctor).p := sorry

/-- Lemma 4.39.4 (1) (Stacks 04SB): the explicit pseudo-pullback of two categories fibred in
setoids over a category fibred in groupoids is again fibred in setoids. This is the convenient
unbundled specialization of `Projection.InSetoids.ofCartesian`. -/
@[stacks 04SB "(1)"]
instance Projection.InSetoids.ofGroupoidTarget
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)
    [Functor.IsFibered.InSetoids X.p]
    [Functor.IsFibered.InSetoids Y.p]
    [Functor.IsFibered.InGroupoids S.p] :
    Functor.IsFibered.InSetoids
      (BasedCategory.PseudoPullback F G).p := sorry
/- Proof strategy: combine `Projection.inGroupoids` with `Projection.faithful`, then apply
`IsFibered.InSetoids.iff_inGroupoids_faithful`. -/

end BasedCategory.PseudoPullback

namespace BasedCategory

namespace isFiberedInSetoids

/-- The chosen pseudo-pullback of cartesian morphisms whose sources are fibred in setoids is again
fibred in setoids. This is the universe-polymorphic object-property form of
`PseudoPullback.Projection.InSetoids.ofCartesian`; the common target need not satisfy a fibredness
property. -/
theorem PseudoPullback.ofCartesian
    {X : BasedCategory.{vX, uX} C}
    {Y : BasedCategory.{vY, uY} C}
    {S : BasedCategory.{vS, uS} C}
    (hX : isFiberedInSetoids C X)
    (hY : isFiberedInSetoids C Y)
    (F : CartesianBasedFunctor X.p S.p)
    (G : CartesianBasedFunctor Y.p S.p) :
    isFiberedInSetoids C
      (PseudoPullback F.toBasedFunctor G.toBasedFunctor) := sorry
/- Proof strategy: install `hX` and `hY` as setoid-fibration instances and apply
`PseudoPullback.Projection.InSetoids.ofCartesian F G`. -/

/-- The chosen pseudo-pullback of setoid-fibred sources over a groupoid-fibred target is again
fibred in setoids. All three total categories may live in independent universes. -/
theorem PseudoPullback.ofGroupoidTarget
    {X : BasedCategory.{vX, uX} C}
    {Y : BasedCategory.{vY, uY} C}
    {S : BasedCategory.{vS, uS} C}
    (hX : isFiberedInSetoids C X)
    (hY : isFiberedInSetoids C Y)
    (hS : isFiberedInGroupoids C S)
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) :
    isFiberedInSetoids C (PseudoPullback F G) := sorry
/- Proof strategy: install `hX`, `hY`, and `hS`, then apply
`PseudoPullback.Projection.InSetoids.ofGroupoidTarget F G`. -/

/-- The chosen pseudo-pullback of a cospan of categories fibred in setoids is again fibred in
setoids. This full-property specialization is convenient for arbitrary-universe object-property
arguments; the stronger target-in-groupoids theorem is
`PseudoPullback.ofGroupoidTarget`. -/
theorem pseudoPullback
    {X : BasedCategory.{vX, uX} C}
    {Y : BasedCategory.{vY, uY} C}
    {S : BasedCategory.{vS, uS} C}
    (hX : isFiberedInSetoids C X)
    (hY : isFiberedInSetoids C Y)
    (hS : isFiberedInSetoids C S)
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) :
    isFiberedInSetoids C (PseudoPullback F G) := sorry
/- Proof strategy: map `hS` along
`BasedCategory.isFiberedInSetoids.le_isFiberedInGroupoids`, then apply
`PseudoPullback.ofGroupoidTarget`. -/

/-- The universe-stable object property of being fibred in setoids is closed under the explicit
based pseudo-pullback. The additional hom universe `vB` is independent of the base-category hom
universe `v`; for unrelated total-category universes, use
`pseudoPullback` directly. -/
instance PseudoPullback.isClosedUnder :
    BasedCategory.PseudoPullback.ObjectProperty.IsClosedUnder
      (isFiberedInSetoids C :
        ObjectProperty
          (BasedCategory.{max v vB, max w (max u (max v vB))} C)) := sorry
/- Proof strategy: specialize `pseudoPullback` to the stable universe chosen by
`BasedCategory.PseudoPullback.ObjectProperty.IsClosedUnder`. -/

end isFiberedInSetoids

end BasedCategory

end CategoryTheory
