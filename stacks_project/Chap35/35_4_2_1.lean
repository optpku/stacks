/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.Shapes.SplitEqualizer
import StacksCheckRecall

@[expose] public section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {A B D : C} {f : A ⟶ B} {g₁ g₂ : B ⟶ D}
variable (equalizes : f ≫ g₁ = f ≫ g₂)

/- 35.4.2.1: for an equalizing diagram `A ⟶ B ⇉ D`, a splitting consists of maps
`h : B ⟶ A` and `i : D ⟶ B` satisfying the three displayed identities. -/
@[stacks 08WI] #check
  (CategoryTheory.IsSplitEqualizer.nonempty_iff_exists equalizes :
    Nonempty (CategoryTheory.IsSplitEqualizer g₁ g₂ f) ↔
      ∃ (h : B ⟶ A) (i : D ⟶ B),
        f ≫ h = 𝟙 A ∧ h ≫ f = g₁ ≫ i ∧ g₂ ≫ i = 𝟙 B)

end CategoryTheory
