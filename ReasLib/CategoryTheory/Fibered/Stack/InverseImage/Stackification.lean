/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification.Pushforward
public import ReasLib.CategoryTheory.Sites.MorphismOfSites
import Mathlib.Tactic.CrossRefAttribute

/-!
# Stackification and inverse image

The neutral compatibility of localized pushforward with two arbitrary stackifications is owned
by `CartesianBasedFunctor.IsStackification.pushforward_comp`.  This file specializes its second
stackification to the comparison carried by a chosen inverse-image stack, first without imposing
a common universe on the total categories and then as a fixed-universe bundled companion.

## Main declarations

* `CategoryTheory.StackOver.InverseImage.Cartesian.pushforwardComparison` — the heterogeneous
  canonical composite from a localized pushforward to the chosen inverse-image stack.
* `CategoryTheory.StackOver.InverseImage.pushforwardComparison` — its fixed-universe bundled
  companion.
* `CategoryTheory.StackOver.InverseImage.pushforwardComparison.isStackification` — stackification
  is stable under the canonical inverse-image comparison; this is a thin specialization of
  `FiberedCategoryOver.Hom.IsStackification.pushforward_comp`.
* `CategoryTheory.StackOver.InverseImage.pushforwardComparison.ofMorphismOfSites` — the
  specialization to a morphism of sites and finite limits.
-/

@[expose] public section

universe uC uD vC vD uX vX uS vS uT vT w₀ w₁

namespace CategoryTheory

open Limits

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

namespace StackOver.InverseImage.Cartesian

variable {X : Type uX} [Category.{vX} X] {p : X ⥤ C} [p.IsFibered]
variable {u : C ⥤ D} {S : StackOver.{uC, vC, uS, vS} J}
variable (I : StackOver.InverseImage.{uC, uD, vC, vD, uS, vS, uT, vT} K u S)

/-- The heterogeneous comparison obtained by pushing forward a cartesian map into the source
stack of an inverse-image choice and then composing with its stored comparison.  The source,
source stack, and target stack may have independent total-category universes. -/
@[stacks 04WR "heterogeneous inverse-image pushforward comparison"]
noncomputable def pushforwardComparison
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (hp : Functor.Pushforward.ProjectionChoice u p)
    (G : CartesianBasedFunctor p S.p)
    (hG : Functor.Pushforward.sourceMap.inverts u G) :
    CartesianBasedFunctor (u.pushforwardProjection p hp) I.target.p :=
  (CartesianBasedFunctor.Pushforward.map u G hp I.sourceChoice.raw hG).comp I.comparison

/-- The based functor underlying the heterogeneous inverse-image pushforward comparison is the
composite of the explicit localized pushforward map and the stored inverse-image comparison. -/
@[simp, stacks 04WR "underlying heterogeneous inverse-image pushforward comparison"]
theorem pushforwardComparison.toBasedFunctor
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (hp : Functor.Pushforward.ProjectionChoice u p)
    (G : CartesianBasedFunctor p S.p)
    (hG : Functor.Pushforward.sourceMap.inverts u G) :
    (pushforwardComparison I hp G hG).toBasedFunctor =
      BasedFunctor.comp
        (CartesianBasedFunctor.Pushforward.map u G hp I.sourceChoice.raw hG).toBasedFunctor
        I.comparison.toBasedFunctor := sorry

/-- The total functor underlying the heterogeneous inverse-image pushforward comparison is the
ordinary composite of the localized pushforward map and the stored comparison functor. -/
@[simp, stacks 04WR "total heterogeneous inverse-image pushforward comparison"]
theorem pushforwardComparison.toFunctor
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (hp : Functor.Pushforward.ProjectionChoice u p)
    (G : CartesianBasedFunctor p S.p)
    (hG : Functor.Pushforward.sourceMap.inverts u G) :
    (pushforwardComparison I hp G hG).toFunctor =
      (CartesianBasedFunctor.Pushforward.map u G hp I.sourceChoice.raw hG).toFunctor ⋙
        I.comparison.toFunctor := sorry

/-- The heterogeneous inverse-image pushforward comparison is a stackification whenever the
source map is one and the base functor is continuous. -/
@[stacks 04WR "heterogeneous inverse image preserves stackification"]
theorem pushforwardComparison.isStackification
    [u.IsContinuous J K]
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    {G : CartesianBasedFunctor p S.p}
    (hG : CartesianBasedFunctor.IsStackification J G)
    (hp : Functor.Pushforward.ProjectionChoice u p)
    (h_inverts : Functor.Pushforward.sourceMap.inverts u G) :
    CartesianBasedFunctor.IsStackification K
      (pushforwardComparison I hp G h_inverts) := sorry

/- Axiom audit: the heterogeneous comparison consists only of an explicit localized map and the
comparison stored in `I`; no proof is converted into non-Prop data. -/

end StackOver.InverseImage.Cartesian

namespace StackOver.InverseImage

/-- Compose the pushforward of a comparison into a stack with the stackification comparison
carried by a chosen inverse-image stack.  Both constituent morphisms are explicit data. -/
@[stacks 04WR "inverse-image pushforward comparison"]
noncomputable def pushforwardComparison
    {u : C ⥤ D}
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    {X : FiberedCategoryOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} C}
    {Y : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}
    (G : X ⟶ Y.toFiberedCategoryOver)
    (hX : FiberedCategoryOver.Pushforward.ProjectionChoice u X)
    (h_inverts : Functor.Pushforward.sourceMap.inverts u
      (FiberedCategoryOver.toCartesianBasedFunctor G))
    (I : StackOver.InverseImage K u Y) :
    FiberedCategoryOver.pushforward u X hX ⟶ I.target.toFiberedCategoryOver :=
  (FiberedCategoryOver.CartesianHom.toHom
      (FiberedCategoryOver.pushforward u X hX) I.target.toFiberedCategoryOver).obj
    (Cartesian.pushforwardComparison I hX.raw
      (FiberedCategoryOver.toCartesianBasedFunctor G) h_inverts)

/-- Forgetting the fixed-universe companion recovers the heterogeneous inverse-image pushforward
comparison. -/
@[simp, stacks 04WR "underlying inverse-image pushforward comparison"]
theorem pushforwardComparison.toCartesianBasedFunctor
    {u : C ⥤ D}
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    {X : FiberedCategoryOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} C}
    {Y : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}
    (G : X ⟶ Y.toFiberedCategoryOver)
    (hX : FiberedCategoryOver.Pushforward.ProjectionChoice u X)
    (h_inverts : Functor.Pushforward.sourceMap.inverts u
      (FiberedCategoryOver.toCartesianBasedFunctor G))
    (I : StackOver.InverseImage K u Y) :
    FiberedCategoryOver.toCartesianBasedFunctor
        (pushforwardComparison G hX h_inverts I) =
      Cartesian.pushforwardComparison I hX.raw
        (FiberedCategoryOver.toCartesianBasedFunctor G) h_inverts := sorry

/-- The canonical limit-shape formulation of stability of stackification under inverse image.

Only pullbacks and equalizers, together with their preservation by `u`, are used by the localized
pushforward construction. This is the reusable core behind Lemma 8.12.11. -/
@[stacks 04WR "inverse image preserves stackification under minimal finite limits"]
theorem pushforwardComparison.isStackification
    {u : C ⥤ D} [u.IsContinuous J K]
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    {X : FiberedCategoryOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} C}
    {Y : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}
    {G : X ⟶ Y.toFiberedCategoryOver}
    (hG : FiberedCategoryOver.Hom.IsStackification J G)
    (hX : FiberedCategoryOver.Pushforward.ProjectionChoice u X)
    (h_inverts : Functor.Pushforward.sourceMap.inverts u
      (FiberedCategoryOver.toCartesianBasedFunctor G))
    (I : StackOver.InverseImage K u Y) :
    FiberedCategoryOver.Hom.IsStackification K
      (pushforwardComparison G hX h_inverts I) := sorry

/-- Lemma 8.12.11 (tag 04WR): inverse image carries a stackification to a stackification.

The source hypotheses that `C` has a terminal object and pullbacks and that `u` preserves them are
expressed by the equivalent mathlib interfaces `HasFiniteLimits C` and `PreservesFiniteLimits u`.
The separate `IsMorphismOfSites J K u` owner records the source's site-morphism hypothesis and
supplies continuity. -/
@[stacks 04WR "inverse image preserves stackification"]
theorem pushforwardComparison.ofMorphismOfSites
    {u : C ⥤ D} [IsMorphismOfSites J K u]
    [HasFiniteLimits C] [PreservesFiniteLimits u]
    {X : FiberedCategoryOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} C}
    {Y : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}
    {G : X ⟶ Y.toFiberedCategoryOver}
    (hG : FiberedCategoryOver.Hom.IsStackification J G)
    (hX : FiberedCategoryOver.Pushforward.ProjectionChoice u X)
    (I : StackOver.InverseImage K u Y) :
    FiberedCategoryOver.Hom.IsStackification K
      (pushforwardComparison G hX
        (Functor.Pushforward.sourceMap.inverts.spec u
          (FiberedCategoryOver.toCartesianBasedFunctor G)) I) := sorry

end StackOver.InverseImage

end CategoryTheory

/- Axiom audit: `pushforwardComparison` is the explicit composite of the chosen pushforward map
and the comparison stored in the inverse-image stack. -/
