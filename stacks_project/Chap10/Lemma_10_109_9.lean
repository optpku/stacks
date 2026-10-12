/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Abelian.Projective.Dimension.ShortExact
import StacksCheckRecall

/-!
# Projective Dimension in Short Exact Sequences

@stack 065S
-/

@[expose] public section

universe u v

open CategoryTheory

section

variable {R : Type u} [Ring R] {S : ShortComplex (ModuleCat.{v} R)}

/- Lemma 10.109.9 (Stacks `065S`): let
`0 ⟶ M' ⟶ M ⟶ M'' ⟶ 0` be a short exact sequence of `R`-modules. The following three recalls
give the projective-dimension bounds for `M'`, `M`, and `M''`, respectively. -/
@[stacks 065S "(1)"]
#check (CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLE_X₁ (S := S) :
  S.ShortExact → ∀ n : ℕ,
    HasProjectiveDimensionLE S.X₂ n →
    HasProjectiveDimensionLE S.X₃ (n + 1) →
    HasProjectiveDimensionLE S.X₁ n)

@[stacks 065S "(2)"]
#check (CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLE_X₂ (S := S) :
  S.ShortExact → ∀ n : ℕ,
    HasProjectiveDimensionLE S.X₁ n →
    HasProjectiveDimensionLE S.X₃ n →
    HasProjectiveDimensionLE S.X₂ n)

@[stacks 065S "(3)"]
#check (CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLE_X₃ (S := S) :
  S.ShortExact → ∀ n : ℕ,
    HasProjectiveDimensionLE S.X₁ n →
    HasProjectiveDimensionLE S.X₂ (n + 1) →
    HasProjectiveDimensionLE S.X₃ (n + 1))

end
