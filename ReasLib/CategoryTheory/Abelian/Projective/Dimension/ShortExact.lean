/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Projective-dimension bounds in short exact sequences

This leaf exposes the successor-shifted `HasProjectiveDimensionLE` view of Mathlib's canonical
`HasProjectiveDimensionLT` short-exact lemmas. The statements live at the natural level of an
arbitrary abelian category; module-category applications are specializations.
-/

@[expose] public section

universe v u

namespace CategoryTheory.ShortComplex.ShortExact

variable {C : Type u} [Category.{v} C] [Abelian C] {S : ShortComplex C}

/-- Lemma 10.109.9 (1) (Stacks `065S`): in a short exact sequence in an abelian category, bounds
on the middle term and cokernel give the corresponding bound on the kernel. -/
@[stacks 065S "(1)"]
theorem hasProjectiveDimensionLE_X₁ (hS : S.ShortExact) (n : ℕ)
    (h₂ : HasProjectiveDimensionLE S.X₂ n)
    (h₃ : HasProjectiveDimensionLE S.X₃ (n + 1)) :
    HasProjectiveDimensionLE S.X₁ n := sorry

/-- Lemma 10.109.9 (2) (Stacks `065S`): in a short exact sequence in an abelian category, bounds
on the kernel and cokernel give the corresponding bound on the middle term. -/
@[stacks 065S "(2)"]
theorem hasProjectiveDimensionLE_X₂ (hS : S.ShortExact) (n : ℕ)
    (h₁ : HasProjectiveDimensionLE S.X₁ n)
    (h₃ : HasProjectiveDimensionLE S.X₃ n) :
    HasProjectiveDimensionLE S.X₂ n := sorry

/-- Lemma 10.109.9 (3) (Stacks `065S`): in a short exact sequence in an abelian category, bounds
on the kernel and middle term give the corresponding bound on the cokernel. -/
@[stacks 065S "(3)"]
theorem hasProjectiveDimensionLE_X₃ (hS : S.ShortExact) (n : ℕ)
    (h₁ : HasProjectiveDimensionLE S.X₁ n)
    (h₂ : HasProjectiveDimensionLE S.X₂ (n + 1)) :
    HasProjectiveDimensionLE S.X₃ (n + 1) := sorry

end CategoryTheory.ShortComplex.ShortExact
