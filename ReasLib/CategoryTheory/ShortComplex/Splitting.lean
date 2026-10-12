/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Complementary maps in split short complexes

For an exact short complex in a balanced preadditive category, either half of a splitting
determines the other half uniquely.
-/

@[expose] public section

universe v u

namespace CategoryTheory.ShortComplex.Splitting

variable {C : Type u} [Category.{v} C] [Preadditive C] [Balanced C]
variable {S : ShortComplex C}

/-- 010G (Lemma 12.5.10 (1)): a section of the final map of an exact short complex determines a
unique complementary retraction of the initial map. -/
@[stacks 010G]
theorem existsUnique_retraction (hS : S.Exact) [Mono S.f]
    (s : S.X₃ ⟶ S.X₂) (hs : s ≫ S.g = 𝟙 S.X₃) :
    ∃! r : S.X₂ ⟶ S.X₁,
      S.f ≫ r = 𝟙 S.X₁ ∧ r ≫ S.f + S.g ≫ s = 𝟙 S.X₂ := sorry

/-- 010G (Lemma 12.5.10 (2)): a retraction of the initial map of an exact short complex determines
a unique complementary section of the final map. -/
@[stacks 010G]
theorem existsUnique_section (hS : S.Exact) [Epi S.g]
    (r : S.X₂ ⟶ S.X₁) (hr : S.f ≫ r = 𝟙 S.X₁) :
    ∃! s : S.X₃ ⟶ S.X₂,
      s ≫ S.g = 𝟙 S.X₃ ∧ r ≫ S.f + S.g ≫ s = 𝟙 S.X₂ := sorry

end CategoryTheory.ShortComplex.Splitting

