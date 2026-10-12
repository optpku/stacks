/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Limits.Preserves.Yoneda

@[expose] public section

namespace CategoryTheory

open Limits

universe u v

namespace Functor.relativelyRepresentable

/-- A relatively representable morphism of presheaves has a relatively representable relative diagonal. -/
theorem pullback_diagonal {C : Type u} [Category.{v} C] [HasPullbacks C]
    {F G : Cᵒᵖ ⥤ Type v} (a : F ⟶ G)
    (ha : yoneda.relativelyRepresentable a) :
    yoneda.relativelyRepresentable (Limits.pullback.diagonal a) := sorry

end Functor.relativelyRepresentable

end CategoryTheory
