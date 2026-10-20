/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Hypercover.Zero

@[expose] public section

universe w₂ w₁ v u

namespace CategoryTheory.PreZeroHypercover

variable {C : Type u} [Category.{v} C] {U V : C}

/-- A morphism of indexed arrow families over a specified base morphism consists of
reindexing and component morphisms commuting with the arrows to the targets. -/
def HomOver (base : U ⟶ V) (source : PreZeroHypercover.{w₁} U)
    (target : PreZeroHypercover.{w₂} V) : Type (max w₁ w₂ v) :=
  Hom (source.pushforward base) target

/-- An indexed arrow family refines another over the same target when there exists
a reindexing with component morphisms commuting with their structure arrows. -/
def Refines (source : PreZeroHypercover.{w₁} U)
    (target : PreZeroHypercover.{w₂} U) : Prop :=
  Nonempty (Hom source target)

/-- Refinement is equivalent to the existence of a family morphism over the identity
of the common target. -/
theorem refines_iff_nonempty_homOver_id (source : PreZeroHypercover.{w₁} U)
    (target : PreZeroHypercover.{w₂} U) :
    Refines source target ↔ Nonempty (HomOver (𝟙 U) source target) := sorry

end CategoryTheory.PreZeroHypercover
