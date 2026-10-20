/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Criteria
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory
namespace Functor

universe v₁ v₂ u₁ u₂

variable {S : Type u₁} [Category.{v₁} S]
variable {C : Type u₂} [Category.{v₂} C]
variable (p : S ⥤ C)

/- Definition 4.33.5: a category `𝒮` over `𝒞` via `p` is fibred exactly when every morphism
`f : V ⟶ p.obj x` admits a strongly cartesian lift `φ : fx ⟶ x` lying over `f`. The canonical
owner remains `Functor.IsFibered`; this theorem is its source-facing existence criterion. -/
@[stacks 02XM "fibred categories via strongly cartesian lifts"]
#check (IsFibered.iff_exists_isStronglyCartesian p :
  p.IsFibered ↔
    ∀ (x : S) (V : C) (f : V ⟶ p.obj x),
      ∃ (fx : S) (φ : fx ⟶ x), p.IsStronglyCartesian f φ)

end Functor
end CategoryTheory
