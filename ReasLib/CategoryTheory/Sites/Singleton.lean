/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.IsSheafFor

/-!
# Singleton sheaf conditions

This module relates descent for singleton presieves along monomorphisms to bijectivity of the
corresponding restriction map.
-/

@[expose] public section

open Opposite

universe u v w

namespace CategoryTheory.Presieve

variable {C : Type u} [Category.{v} C]

/-- For a monomorphism, the sheaf condition for its singleton presieve is equivalent to
bijectivity of the corresponding restriction map. -/
theorem isSheafFor_singleton_iff_bijective_of_mono (F : Cᵒᵖ ⥤ Type w)
    {X Y : C} (f : X ⟶ Y) [Mono f] :
    IsSheafFor F (singleton f) ↔ Function.Bijective (F.map f.op) := sorry

end CategoryTheory.Presieve
