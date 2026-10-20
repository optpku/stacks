/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
import ReasLib.CategoryTheory.Fibered.Groupoids.FiberwiseEquivalence
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.BaseChange

/-!
# Faithfulness of relatively representable morphisms

The narrow 02Y8 consequence, separated from fiber-pair representability and the converse
criterion so downstream users can import faithfulness without the full criterion layer.
-/

@[expose] public section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.Groupoids C}

namespace FiberedCategoryOver.Groupoids.relativelyRepresentable

/-- Lemma 4.42.4 (Stacks 02Y8): a relatively representable morphism is faithful on every
fiber. -/
@[stacks 02Y8]
theorem fiberwiseFaithful
    {F : X ⟶ Y} (hF : relativelyRepresentable F) (U : C) :
    (fiberFunctor F U).Faithful := sorry

/-- The underlying based functor of a relatively representable morphism is faithful. -/
@[stacks 02Y8 "total functor is faithful"]
theorem faithful
    {F : X ⟶ Y} (hF : relativelyRepresentable F) :
    (toBasedFunctor F).Faithful := sorry

end FiberedCategoryOver.Groupoids.relativelyRepresentable

end CategoryTheory
