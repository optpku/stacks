/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 08NQ

# Right lifting properties and inverse sequences

A right lifting property is stable under every projection from the inverse limit of a countable
tower whose transition maps all have that lifting property.
-/

@[expose] public section

open CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C]

/-- For a countable inverse tower whose transition maps lie in `T.rlp`, every limit projection
also lies in `T.rlp`. -/
@[stacks 08NQ "right lifting properties of inverse-sequence projections"]
theorem rlp.limitProjection (T : MorphismProperty C)
    {X : ℕ → C} (f : ∀ n : ℕ, X (n + 1) ⟶ X n)
    (i : ℕ) [HasLimit (Functor.ofOpSequence f)]
    (hf : ∀ n : ℕ, T.rlp (f n)) :
    T.rlp (limit.π (Functor.ofOpSequence f) (Opposite.op i)) := sorry

end CategoryTheory.MorphismProperty
