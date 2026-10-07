module

public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The Mittag-Leffler Condition

A sequential inverse system in a category with images satisfies the Mittag-Leffler condition
when the images of the transition maps eventually stabilize.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory

namespace SequentialInverseSystem

variable {A : Type u} [Category.{v} A] [HasImages A]

/-- A sequential inverse system satisfies the Mittag-Leffler
condition when, at every index `i`, the images of the transition maps `F(k) ⟶ F(i)` stabilize
for sufficiently large `k`. -/
@[stacks 02N0]
def IsMittagLeffler (F : SequentialInverseSystem A) : Prop :=
  ∀ i : ℕ, ∃ (c : ℕ) (hic : i ≤ c),
    ∀ ⦃k : ℕ⦄ (hck : c ≤ k),
      imageSubobject (F.transitionMap (hic.trans hck)) =
        imageSubobject (F.transitionMap hic)

end SequentialInverseSystem

end CategoryTheory
