module

public import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Tactic.CrossRefAttribute

/-!
# Injective abelian groups

@stack 01D7

This leaf completes Mathlib's implication from divisibility to injectivity with the converse
characterization by surjective multiplication maps.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AddCommGrpCat

variable (J : Type u) [AddCommGroup J]

/-- Lemma 15.54.1 (01D7): an abelian group is injective in `AddCommGrpCat` if and only if
multiplication by every nonzero integer is surjective. -/
@[stacks 01D7 "injective abelian groups are exactly the divisible groups"]
theorem injective_iff_divisible :
    Injective (AddCommGrpCat.of J) ↔
      ∀ n : ℤ, n ≠ 0 → Function.Surjective (n • · : J → J) := sorry

end AddCommGrpCat
