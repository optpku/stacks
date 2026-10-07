module

public import ReasLib.RingTheory.Polynomial.Numerical
import Mathlib.Tactic.CrossRefAttribute

/-!
# Closure properties of numerical polynomials

The predicate `IsNumericalPolynomial` is closed under the additive operations and under
postcomposition by an additive homomorphism.  These statements are kept separate from the
binomial-basis definition so that users of the closure API do not need to import chapter files.

@stack 00JY
-/

@[expose] public section

universe u v

open Filter

namespace IsNumericalPolynomial

/-- Eventual equality transports numerical-polynomiality to the left-hand function. -/
@[stacks 00JY "eventual equality closure"]
theorem congr {A : Type u} [AddCommGroup A] {f g : ℤ → A}
    (hg : IsNumericalPolynomial g) (hfg : f =ᶠ[atTop] g) :
    IsNumericalPolynomial f := by
  rcases hg with ⟨r, hr⟩
  exact ⟨r, hr.congr hfg.symm⟩

/-- Postcomposition by an additive homomorphism preserves numerical-polynomiality. -/
@[stacks 00JY]
theorem comp {A : Type u} [AddCommGroup A] {A' : Type v} [AddCommGroup A']
    {f : ℤ → A} (hf : IsNumericalPolynomial f) (φ : A →+ A') :
    IsNumericalPolynomial (φ ∘ f) := by
  rcases hf with ⟨r, a, ha⟩
  refine ⟨r, ⟨fun i ↦ φ (a i), ?_⟩⟩
  filter_upwards [ha] with n hn
  simp only [Function.comp_apply, hn, map_sum, map_zsmul]

/-- Numerical-polynomial functions are closed under pointwise addition. -/
@[stacks 00JY "additive closure"]
theorem add {A : Type u} [AddCommGroup A] {f g : ℤ → A}
    (hf : IsNumericalPolynomial f) (hg : IsNumericalPolynomial g) :
    IsNumericalPolynomial (f + g) := sorry

/-- The zero-valued function is a numerical polynomial. -/
@[stacks 00JY "zero closure"]
theorem zero {A : Type u} [AddCommGroup A] :
    IsNumericalPolynomial (0 : ℤ → A) :=
  of_eventuallyEq_zero (Filter.Eventually.of_forall fun _ ↦ rfl)

/-- Numerical-polynomial functions are closed under pointwise negation. -/
@[stacks 00JY "negation closure"]
theorem neg {A : Type u} [AddCommGroup A] {f : ℤ → A}
    (hf : IsNumericalPolynomial f) : IsNumericalPolynomial (-f) := by
  change IsNumericalPolynomial (fun x ↦ -f x)
  exact comp hf (-AddMonoidHom.id A)

/-- Numerical-polynomial functions are closed under pointwise subtraction. -/
@[stacks 00JY "subtraction closure"]
theorem sub {A : Type u} [AddCommGroup A] {f g : ℤ → A}
    (hf : IsNumericalPolynomial f) (hg : IsNumericalPolynomial g) :
    IsNumericalPolynomial (f - g) := by
  simpa [sub_eq_add_neg] using add hf hg.neg

end IsNumericalPolynomial
