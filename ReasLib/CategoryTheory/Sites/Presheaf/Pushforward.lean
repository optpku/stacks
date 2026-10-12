/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

@[expose] public section

open CategoryTheory

noncomputable section

universe u v u' v' w

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C]
variable {C' : Type u'} [Category.{v'} C']

/-! The right Kan extension gives the covariant pushforward operation on presheaves. -/

/-- The pushforward functor on `Type w`-valued presheaves induced by `u : C' ⥤ C`. -/
noncomputable def presheafPushforward (u : C' ⥤ C)
    [∀ F : C'ᵒᵖ ⥤ Type w, HasRightKanExtension u.op F] :
    (C'ᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w) :=
  u.op.ran

end CategoryTheory.Functor

end
