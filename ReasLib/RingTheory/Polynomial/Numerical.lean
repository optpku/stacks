module

public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.CrossRefAttribute

/-!
# Numerical polynomials

The Stacks convention treats a numerical polynomial as an eventual binomial-basis expansion.
The reusable formulation below uses a total function on `ℤ` and `Filter.Eventually` at `atTop`;
this keeps the predicate composable under additive maps and avoids a partial-function carrier.
-/

@[expose] public section

universe u

open Filter
open scoped BigOperators

variable {A : Type u} [AddCommGroup A]

namespace IsNumericalPolynomial

/-- A function has a binomial-basis expansion of the indicated finite length eventually.

This witness-level predicate is shared by degree bounds and representative constructions; callers
should use it instead of repeating the eventual finite sum. -/
@[stacks 00JX "eventual binomial-basis expansion"]
def hasExpansion (f : ℤ → A) (r : ℕ) : Prop :=
  ∃ a : Fin (r + 1) → A,
    f =ᶠ[atTop] fun n ↦ ∑ i : Fin (r + 1), Ring.choose n (i : ℕ) • a i

end IsNumericalPolynomial

/-- A function is a numerical polynomial when it is eventually a finite binomial-basis polynomial
with coefficients in the additive commutative group `A`. -/
@[stacks 00JX]
def IsNumericalPolynomial (f : ℤ → A) : Prop :=
  ∃ r : ℕ, IsNumericalPolynomial.hasExpansion f r

namespace IsNumericalPolynomial

/-- An eventual binomial-basis expansion is a numerical polynomial. -/
@[stacks 00JX "binomial-basis expansion is numerical polynomial"]
theorem hasExpansion.isNumericalPolynomial {f : ℤ → A} {r : ℕ}
    (hf : IsNumericalPolynomial.hasExpansion f r) : IsNumericalPolynomial f :=
  ⟨r, hf⟩

/-- Eventual equality transports an expansion without changing its length. -/
@[stacks 00JX "transport of a binomial-basis expansion"]
theorem hasExpansion.congr {f g : ℤ → A} {r : ℕ}
    (hf : IsNumericalPolynomial.hasExpansion f r) (hfg : f =ᶠ[atTop] g) :
    IsNumericalPolynomial.hasExpansion g r := by
  rcases hf with ⟨a, ha⟩
  exact ⟨a, hfg.symm.trans ha⟩

/-- An eventually zero function is a numerical polynomial. -/
@[stacks 00JX "eventually zero numerical polynomial"]
theorem of_eventuallyEq_zero {f : ℤ → A}
    (hf : f =ᶠ[atTop] fun _ ↦ (0 : A)) : IsNumericalPolynomial f := by
  refine ⟨0, ⟨fun _ ↦ 0, ?_⟩⟩
  simpa using hf

end IsNumericalPolynomial
