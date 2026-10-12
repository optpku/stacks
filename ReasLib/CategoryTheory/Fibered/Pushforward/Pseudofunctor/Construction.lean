/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Pushforward.Pseudofunctor.Coherence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pushforward pseudofunctor construction

This leaf packages the chosen object, `1`-cell, and `2`-cell actions and their local coherence as
a pseudofunctor on fibred categories.
-/

@[expose] public section

universe uC uD vC vD w₀ w₁

namespace CategoryTheory

open Bicategory Limits
open scoped Bicategory

namespace FiberedCategoryOver.Pushforward

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable (u : C ⥤ D) [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]

/-- 04WI: pushforward along `u` as a pseudofunctor on fibred categories.

Its object, `1`-cell, and `2`-cell actions are the existing computational owners
`FiberedCategoryOver.pushforward`, `map`, and `map₂`. The inversion and comparison choices are
explicit inputs; this declaration adds only the bicategorical coherence packaging. -/
@[stacks 04WI "pushforward pseudofunctor"]
noncomputable def pseudofunctor
    (h : CoherentInversionChoice u) :
  Pseudofunctor
      (FiberedCategoryOver.{uC, vC, w₀, w₁} C)
      (FiberedCategoryOver.{uD, vD,
        max w₀ (max uC (max uD (max vC vD))),
        max w₁ (max w₀ (max uC (max uD (max vC vD))))} D) where
  toPrelaxFunctor := h.prelax
  mapId := h.mapId
  mapComp := h.mapComp
  map₂_whisker_left := h.map₂_whisker_left
  map₂_whisker_right := h.map₂_whisker_right
  map₂_associator := h.map₂_associator
  map₂_left_unitor := h.map₂_left_unitor
  map₂_right_unitor := h.map₂_right_unitor

end FiberedCategoryOver.Pushforward

end CategoryTheory

-- Data audit: the pseudofunctor packages the explicit comparison isomorphisms and coherence
-- fields supplied by `CoherentInversionChoice`; no equality-to-isomorphism transport is introduced.
