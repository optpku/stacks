/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Pushforward
public import ReasLib.CategoryTheory.Fibered.Groupoids.Bicategory
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pushforward of categories fibred in groupoids

The localized pushforward of a category fibred in groupoids is again fibred in groupoids under
the finite-limit hypotheses used to construct the pushforward projection.  This is independent
of any topology or stack condition.

## Main declarations

* `Functor.Pushforward.projectionInGroupoids` — the projection-level preservation
  theorem.
* `FiberedCategoryOver.Groupoids.Pushforward.ProjectionChoice` — explicit projection
  certification at the groupoid-fibred layer.
* `FiberedCategoryOver.Groupoids.pushforward` — the bundled pushforward construction.
-/

@[expose] public section

universe uC uD uS vC vD vS

namespace CategoryTheory

open Limits

namespace Functor

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]

/-- Lemma 8.12.7 (tag 04WH): an explicitly chosen localized pushforward projection of a
category fibred in groupoids is again fibred in groupoids. -/
@[stacks 04WH]
theorem Pushforward.projectionInGroupoids
    (u : C ⥤ D) (p : S ⥤ C) [Functor.IsFibered.InGroupoids p]
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (h : Pushforward.ProjectionChoice u p) :
    Functor.IsFibered.InGroupoids (u.pushforwardProjection p h) := sorry

end Functor

namespace FiberedCategoryOver.Groupoids

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]

namespace Pushforward

/-- The explicit projection choice needed to bundle a localized pushforward as a category
fibred in groupoids. -/
@[stacks 04WH]
structure ProjectionChoice (u : C ⥤ D) (X : FiberedCategoryOver.Groupoids C) : Prop where
  /-- The prelocalized projection inverts the pushforward fractions. -/
  inverts : (u.pushforwardFractions X.p).IsInvertedBy
    (Functor.Pushforward.sourceProjection u X.p)
  /-- The explicitly induced projection is fibred in groupoids. -/
  inGroupoids : Functor.IsFibered.InGroupoids
    (Functor.Pushforward.projection u X.p inverts)

/-- The canonical groupoid-fibred projection choice obtained from the localization construction
under the standard finite-limit hypotheses.
-/
@[stacks 04WH "canonical groupoid-fibred pushforward choice"]
theorem ProjectionChoice.canonical (u : C ⥤ D) (X : FiberedCategoryOver.Groupoids C)
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    ProjectionChoice u X := sorry

/-- Forget a groupoid-fibred projection choice to its raw fraction-inversion component. -/
@[stacks 04WH "groupoid-fibred pushforward raw choice"]
theorem ProjectionChoice.raw {u : C ⥤ D} {X : FiberedCategoryOver.Groupoids C}
    (h : ProjectionChoice u X) : Functor.Pushforward.ProjectionChoice u X.p := sorry

/-- Forget a groupoid-fibred projection choice to the ordinary fibred-category choice on the
same underlying projection. -/
@[stacks 04WH "groupoid-fibred pushforward ordinary choice"]
theorem ProjectionChoice.toFibered {u : C ⥤ D} {X : FiberedCategoryOver.Groupoids C}
    (h : ProjectionChoice u X) :
    FiberedCategoryOver.Pushforward.ProjectionChoice u
      ((FiberedCategoryOver.Groupoids.toFibered C).obj X) := sorry

/-- Enrich a raw pushforward projection choice with an explicitly supplied proof that the
selected projection is fibred in groupoids. -/
@[stacks 04WH "groupoid-fibred pushforward choice from raw data"]
theorem ProjectionChoice.ofRawWith {u : C ⥤ D} (X : FiberedCategoryOver.Groupoids C)
    (h : Functor.Pushforward.ProjectionChoice u X.p)
    (h_groupoids : Functor.IsFibered.InGroupoids (u.pushforwardProjection X.p h)) :
    ProjectionChoice u X := sorry

/-- Enrich a raw pushforward projection choice using the canonical groupoid-fibredness theorem
for the localized projection under the finite-limit hypotheses. -/
@[stacks 04WH "canonical groupoid-fibred pushforward choice from raw data"]
theorem ProjectionChoice.ofRaw {u : C ⥤ D} (X : FiberedCategoryOver.Groupoids C)
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (h : Functor.Pushforward.ProjectionChoice u X.p) : ProjectionChoice u X := sorry

end Pushforward

/-- Lemma 8.12.7 (tag 04WH): the bundled pushforward of a category fibred in groupoids formed
from an explicit projection choice. -/
@[stacks 04WH "bundled groupoid-fibred pushforward"]
noncomputable def pushforward (u : C ⥤ D) (X : FiberedCategoryOver.Groupoids C)
    (h : Pushforward.ProjectionChoice u X) :
    FiberedCategoryOver.Groupoids D :=
  ⟨BasedCategory.ofFunctor (Functor.Pushforward.projection u X.p h.inverts), h.inGroupoids⟩

/- Axiom audit: the total category and projection are the explicit localization lifting determined
by `h.inverts`; `h.inGroupoids` contributes only the Prop-valued object-membership field. -/

/-- The total category of a bundled groupoid-fibred pushforward is the localization at the
pushforward fractions. -/
@[simp, stacks 04WH "groupoid-fibred pushforward total computation"]
theorem pushforward.total (u : C ⥤ D) (X : FiberedCategoryOver.Groupoids C)
    (h : Pushforward.ProjectionChoice u X) :
    (pushforward u X h).total = Functor.pushforward u X.p := sorry

/-- Lemma 8.12.7 (tag 04WH): the projection of the bundled groupoid-fibred pushforward is the
localized projection selected by the explicit choice. -/
@[simp, stacks 04WH "groupoid-fibred pushforward projection computation"]
theorem pushforward.p (u : C ⥤ D) (X : FiberedCategoryOver.Groupoids C)
    (h : Pushforward.ProjectionChoice u X) :
    (pushforward u X h).p = Functor.Pushforward.projection u X.p h.inverts := sorry

/-- Forgetting the groupoid-fibre refinement of a pushforward recovers the ordinary bundled
pushforward formed from the same projection choice. -/
@[simp, stacks 04WH "groupoid-fibred pushforward ordinary computation"]
theorem pushforward.toFibered (u : C ⥤ D) (X : FiberedCategoryOver.Groupoids C)
    (h : Pushforward.ProjectionChoice u X) :
    (FiberedCategoryOver.Groupoids.toFibered D).obj (pushforward u X h) =
      FiberedCategoryOver.pushforward u
        ((FiberedCategoryOver.Groupoids.toFibered C).obj X) h.toFibered := sorry

end FiberedCategoryOver.Groupoids

end CategoryTheory

-- Expected audit: `ProjectionChoice` is Prop-valued, while its constructor theorems carry only
-- proof debt. The bundled `pushforward` uses only the explicitly supplied projection and
-- groupoid-fibredness fields.
