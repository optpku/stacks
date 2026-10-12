/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Pseudofunctor.Coherence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Inverse image as a pseudofunctor

This file packages a coherent global inverse-image choice into a pseudofunctor.  All
noncanonical object, Hom, identity, and composition data remain visible in the input owner.
-/

@[expose] public section

universe uC uD vC vD w₀ w₁

namespace CategoryTheory

open Bicategory Limits
open scoped Bicategory

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

namespace StackOver.InverseImage

variable (u : C ⥤ D)
variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]

/-- Inverse image along `u` as the pseudofunctor selected by a coherent global choice. -/
@[stacks 04WS "inverse-image pseudofunctor"]
noncomputable def pseudofunctor
    (h : CoherentPseudofunctorChoice (J := J) (K := K) u) :
    Pseudofunctor
      (StackOver.{uC, vC,
        max w₀ (max uC (max uD (max vC vD))),
        max w₁ (max w₀ (max uC (max uD (max vC vD))))} J)
      (StackOver.{uD, vD,
        max w₀ (max uC (max uD (max vC vD))),
        max w₁ (max w₀ (max uC (max uD (max vC vD))))} K) where
  toPrelaxFunctor := h.toChoice.prelax
  mapId := h.mapId
  mapComp := h.mapComp
  map₂_whisker_left := h.map₂_whisker_left
  map₂_whisker_right := h.map₂_whisker_right
  map₂_associator := h.map₂_associator
  map₂_left_unitor := h.map₂_left_unitor
  map₂_right_unitor := h.map₂_right_unitor

-- Data audit: the definition only packages the explicitly supplied choice and coherence fields.

end StackOver.InverseImage

end CategoryTheory
