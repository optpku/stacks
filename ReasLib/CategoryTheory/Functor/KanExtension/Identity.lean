/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import Mathlib.CategoryTheory.Opposites

/-!
# Left Kan extensions along identity functors
-/

@[expose] public section

universe u₁ v₁ u₂ v₂

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- Every functor has a left Kan extension along the identity functor. -/
instance hasLeftKanExtensionId (P : C ⥤ D) : (𝟭 C).HasLeftKanExtension P :=
  HasLeftKanExtension.mk P P.leftUnitor.inv

/-- Every functor on an opposite category has a left Kan extension along the opposite
of the identity functor. -/
instance hasLeftKanExtensionOpId (P : Cᵒᵖ ⥤ D) : (𝟭 C).op.HasLeftKanExtension P :=
  (hasLeftExtension_iff_of_iso₁ (opId C) P).mpr (hasLeftKanExtensionId P)

end CategoryTheory.Functor
