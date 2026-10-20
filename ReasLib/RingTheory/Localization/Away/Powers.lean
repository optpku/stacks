/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Principal localizations and power factorizations

The localization away from an element is unchanged when the two elements
divide powers of one another.  This criterion is independent of blowups and
is therefore owned by the principal-localization support library.
-/

@[expose] public section

universe u v

namespace IsLocalization.Away

variable {A : Type u} {S : Type v}
variable [CommSemiring A] [CommSemiring S] [Algebra A S]

/-- If each of `a` and `f` divides a power of the other, an `a`-localization is
also an `f`-localization. -/
@[stacks 080U "principal localization from mutual power divisibility"]
theorem of_mutual_pow_dvd
    (a f : A) [IsLocalization.Away a S]
    (ha : ∃ n : ℕ, f ∣ a ^ n)
    (hf : ∃ m : ℕ, a ∣ f ^ m) :
    IsLocalization.Away f S := sorry

/-- A product-factorization form of
`IsLocalization.Away.of_mutual_pow_dvd`, convenient when the witnesses arise
from ideal-power containments. -/
@[stacks 080U "principal localization from mutual power factorizations"]
theorem of_pow_factorizations
    (a f : A) [IsLocalization.Away a S]
    (ha : ∃ n : ℕ, ∃ b : A, a ^ n = f * b)
    (hf : ∃ m : ℕ, ∃ c : A, f ^ m = a * c) :
    IsLocalization.Away f S := sorry

end IsLocalization.Away
