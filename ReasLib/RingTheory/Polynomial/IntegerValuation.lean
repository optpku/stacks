module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.Multiplicity
public import Mathlib.RingTheory.Valuation.Basic

@[expose] public section

noncomputable section

open Polynomial

universe u

namespace Polynomial

variable {k : Type u} [Field k]

/-- An integer-valued additive valuation on `k[X]`: multiplicative on nonzero
products, nonarchimedean on nonzero sums, and trivial on nonzero constants. -/
class IsIntegerValuation (ν : k[X] → ℤ) : Prop where
  /-- Multiplicativity on nonzero polynomials. -/
  map_mul : ∀ ⦃f g : k[X]⦄, f ≠ 0 → g ≠ 0 → ν (f * g) = ν f + ν g
  /-- The nonarchimedean inequality on nonzero sums. -/
  map_add : ∀ ⦃f g : k[X]⦄, f ≠ 0 → g ≠ 0 → f + g ≠ 0 → min (ν f) (ν g) ≤ ν (f + g)
  /-- Nonzero constants have value `0`. -/
  map_C : ∀ ⦃c : k⦄, c ≠ 0 → ν (C c) = 0

/-- An integer valuation is characterized by multiplicativity, the nonarchimedean
inequality, and triviality on nonzero constants. -/
theorem isIntegerValuation_iff (ν : k[X] → ℤ) :
    IsIntegerValuation ν ↔
      (∀ ⦃f g : k[X]⦄, f ≠ 0 → g ≠ 0 → ν (f * g) = ν f + ν g) ∧
        (∀ ⦃f g : k[X]⦄, f ≠ 0 → g ≠ 0 → f + g ≠ 0 → min (ν f) (ν g) ≤ ν (f + g)) ∧
          (∀ ⦃c : k⦄, c ≠ 0 → ν (C c) = 0) := sorry

namespace IsIntegerValuation

variable (ν : k[X] → ℤ) [IsIntegerValuation ν]

/-- The unit polynomial has value `0`. -/
theorem map_one : ν 1 = 0 := sorry

/-- Integer valuations are even: `ν (-f) = ν f` for `f ≠ 0`. -/
theorem map_neg {f : k[X]} (hf : f ≠ 0) : ν (-f) = ν f := sorry

/-- The extension of an integer-valued function sends zero to `⊤` and a nonzero
polynomial `f` to `(ν f : WithTop ℤ)`, independently of `ν 0`. -/
def extend : k[X] → WithTop ℤ :=
  fun f ↦
    match Classical.propDecidable (f = 0) with
    | .isTrue _ => ⊤
    | .isFalse _ => (ν f : WithTop ℤ)

/-- The extended integer valuation sends zero to `⊤`. -/
theorem extend_zero : extend ν 0 = ⊤ := sorry

/-- The extended integer valuation sends one to zero. -/
theorem extend_one : extend ν 1 = 0 := sorry

/-- The extended integer valuation satisfies the nonarchimedean inequality
without nonzero restrictions. -/
theorem extend_add (f g : k[X]) :
    min (extend ν f) (extend ν g) ≤ extend ν (f + g) := sorry

/-- The extended integer valuation is additive on products without nonzero
restrictions. -/
theorem extend_mul (f g : k[X]) :
    extend ν (f * g) = extend ν f + extend ν g := sorry

end IsIntegerValuation

/-- The zero map on `k[X]`, i.e. the trivial integer valuation. -/
def trivialValuation : k[X] → ℤ := fun _ ↦ 0

/-- The trivial valuation sends every polynomial to `0`. -/
theorem trivialValuation_apply (f : k[X]) : trivialValuation f = 0 := sorry

/-- The zero map is an integer valuation. -/
instance instIsIntegerValuation_trivialValuation : IsIntegerValuation (trivialValuation : k[X] → ℤ) :=
  sorry

/-- The scaled negative-degree map `f ↦ -n * natDegree f`, including the zero
map at `n = 0`. -/
def scaledNegDegree (n : ℕ) : k[X] → ℤ :=
  fun f ↦ -(n : ℤ) * f.natDegree

/-- The scaled negative-degree map evaluates to `-n * natDegree f`. -/
theorem scaledNegDegree_apply (n : ℕ) (f : k[X]) :
    scaledNegDegree n f = -(n : ℤ) * f.natDegree := sorry

/-- Every scaled negative-degree map is an integer valuation. -/
instance instIsIntegerValuation_scaledNegDegree (n : ℕ) :
    IsIntegerValuation (scaledNegDegree n : k[X] → ℤ) := sorry

/-- The scaled prime-multiplicity map `f ↦ n * multiplicity p f`. -/
def scaledMultiplicity (p : k[X]) (n : ℕ) : k[X] → ℤ :=
  fun f ↦ n * (multiplicity p f : ℤ)

/-- The scaled multiplicity map evaluates to `n * multiplicity p f`. -/
theorem scaledMultiplicity_apply (p : k[X]) (n : ℕ) (f : k[X]) :
    scaledMultiplicity p n f = n * (multiplicity p f : ℤ) := sorry

/-- A multiple of the `p`-adic multiplicity is an integer valuation when `p` is
prime. -/
instance instIsIntegerValuation_scaledMultiplicity (p : k[X]) (n : ℕ) [Fact (Prime p)] :
    IsIntegerValuation (scaledMultiplicity p n) := sorry

/-- The `WithTop ℤ`-valued additive valuation extending `ν` on nonzero polynomials
and sending zero to `⊤`. -/
def toAddValuation (ν : k[X] → ℤ) [IsIntegerValuation ν] : AddValuation k[X] (WithTop ℤ) :=
  AddValuation.of (IsIntegerValuation.extend ν)
    (IsIntegerValuation.extend_zero ν) (IsIntegerValuation.extend_one ν)
    (IsIntegerValuation.extend_add ν) (IsIntegerValuation.extend_mul ν)

/-- On nonzero polynomials, `toAddValuation ν` agrees with `ν`. -/
theorem toAddValuation_apply_of_ne_zero (ν : k[X] → ℤ) [IsIntegerValuation ν]
    {f : k[X]} (hf : f ≠ 0) : toAddValuation ν f = (ν f : WithTop ℤ) := sorry

/-- The extended additive valuation sends `0` to `⊤`. -/
theorem toAddValuation_apply_zero (ν : k[X] → ℤ) [IsIntegerValuation ν] :
    toAddValuation ν 0 = ⊤ := sorry

/-- If `f`, `g`, and `f + g` are nonzero and `ν f ≠ ν g`, then the value of the
sum is the minimum of the summands' values. -/
theorem map_add_eq_min (ν : k[X] → ℤ) [IsIntegerValuation ν] {f g : k[X]}
    (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0) (hne : ν f ≠ ν g) :
    ν (f + g) = min (ν f) (ν g) := sorry

/-- The Gauss lower bound for `ν` at a nonzero polynomial: the infimum of
`i * ν X` over the support of `f`. -/
def gaussMin (ν : k[X] → ℤ) {f : k[X]} (hf : f ≠ 0) : ℤ :=
  f.support.inf' (support_nonempty.mpr hf) fun i ↦ (i : ℤ) * ν X

/-- The Gauss minimum equals the infimum of `i * ν X` over the support. -/
theorem gaussMin_def (ν : k[X] → ℤ) {f : k[X]} (hf : f ≠ 0) :
    gaussMin ν hf = f.support.inf' (support_nonempty.mpr hf) fun i ↦ (i : ℤ) * ν X := sorry

/-- The value of a nonzero polynomial is at least the minimum of `i * ν X` over
the degrees of its nonzero coefficients. -/
theorem gauss_le (ν : k[X] → ℤ) [IsIntegerValuation ν] {f : k[X]} (hf : f ≠ 0) :
    gaussMin ν hf ≤ ν f := sorry

/-- Equality holds in the Gauss lower bound if and only if either `ν X ≠ 0`
(so the infimum is attained at a unique degree) or else `ν f = 0`. -/
theorem gauss_eq_iff (ν : k[X] → ℤ) [IsIntegerValuation ν] {f : k[X]} (hf : f ≠ 0) :
    ν f = gaussMin ν hf ↔ ν X ≠ 0 ∨ ν f = 0 := sorry

/-- `ν` attains a negative value on a nonzero polynomial if and only if `ν X < 0`. -/
theorem exists_neg_iff_neg_X (ν : k[X] → ℤ) [IsIntegerValuation ν] :
    (∃ f : k[X], f ≠ 0 ∧ ν f < 0) ↔ ν X < 0 := sorry

/-- An integer valuation attaining a negative value agrees with negative degree
scaled by `(-(ν X)).toNat` on every nonzero polynomial. -/
theorem eq_scaledNegDegree_of_exists_neg (ν : k[X] → ℤ) [IsIntegerValuation ν]
    (hneg : ∃ f : k[X], f ≠ 0 ∧ ν f < 0) {g : k[X]} (hg : g ≠ 0) :
    ν g = scaledNegDegree (-(ν X)).toNat g := sorry

/-- If `ν X ≥ 0`, then `ν` is nonnegative on every nonzero polynomial. -/
theorem nonneg_of_nonneg_X (ν : k[X] → ℤ) [IsIntegerValuation ν] (hX : 0 ≤ ν X)
    {f : k[X]} (hf : f ≠ 0) : 0 ≤ ν f := sorry

namespace IsIntegerValuation

variable (ν : k[X] → ℤ) [IsIntegerValuation ν]

/-- Zero belongs to the union of zero and the strictly positive valuation locus. -/
theorem strictPos_zero : (0 : k[X]) = 0 ∨ 0 < ν 0 := sorry

/-- The union of zero and the strictly positive valuation locus is closed under
addition. -/
theorem strictPos_add {f g : k[X]} (hf : f = 0 ∨ 0 < ν f) (hg : g = 0 ∨ 0 < ν g) :
    f + g = 0 ∨ 0 < ν (f + g) := sorry

/-- When `ν X ≥ 0`, the union of zero and the strictly positive valuation locus
is closed under multiplication by any polynomial. -/
theorem strictPos_smul (hX : 0 ≤ ν X) (r : k[X]) {f : k[X]} (hf : f = 0 ∨ 0 < ν f) :
    r • f = 0 ∨ 0 < ν (r • f) := sorry

end IsIntegerValuation

/-- The set `{f | f = 0 ∨ 0 < ν f}`, as an ideal of `k[X]` when `ν X ≥ 0`. -/
def strictPosIdeal (ν : k[X] → ℤ) [IsIntegerValuation ν] (hX : 0 ≤ ν X) : Ideal k[X] where
  carrier := {f | f = 0 ∨ 0 < ν f}
  add_mem' := IsIntegerValuation.strictPos_add ν
  zero_mem' := IsIntegerValuation.strictPos_zero ν
  smul_mem' := fun r _ hf ↦ IsIntegerValuation.strictPos_smul ν hX r hf

/-- Membership in `strictPosIdeal ν hX` means being zero or having strictly
positive valuation. -/
theorem mem_strictPosIdeal_iff (ν : k[X] → ℤ) [IsIntegerValuation ν] (hX : 0 ≤ ν X)
    {f : k[X]} : f ∈ strictPosIdeal ν hX ↔ f = 0 ∨ 0 < ν f := sorry

namespace strictPosIdeal

/-- If `ν X ≥ 0`, the ideal of zero and strictly positive valuation polynomials
is prime. -/
theorem isPrime (ν : k[X] → ℤ) [IsIntegerValuation ν] (hX : 0 ≤ ν X) :
    (strictPosIdeal ν hX).IsPrime := sorry

end strictPosIdeal

/-- Every integer valuation trivial on constants is either a scaled negative
degree, including scale zero, or a strictly positive scaled prime multiplicity
on nonzero polynomials. -/
theorem eq_scaledNegDegree_or_scaledMultiplicity (ν : k[X] → ℤ) [IsIntegerValuation ν] :
    (∃ n : ℕ, ∀ f : k[X], f ≠ 0 → ν f = scaledNegDegree n f) ∨
      ∃ p : k[X], ∃ n : ℕ, Prime p ∧ 0 < n ∧
        ∀ f : k[X], f ≠ 0 → ν f = scaledMultiplicity p n f := sorry

/-- The natural-number scale of a negative-degree model is unique. -/
theorem scaledNegDegree_scale_unique {n m : ℕ}
    (h : ∀ f : k[X], f ≠ 0 → scaledNegDegree n f = scaledNegDegree m f) : n = m := sorry

/-- The natural-number scale of a strictly positive multiplicity model is unique. -/
theorem scaledMultiplicity_scale_unique {p q : k[X]} {n m : ℕ}
    (hp : Prime p) (hq : Prime q) (hn : 0 < n) (hm : 0 < m)
    (h : ∀ f : k[X], f ≠ 0 → scaledMultiplicity p n f = scaledMultiplicity q m f) :
    n = m := sorry

/-- The prime in a strictly positive multiplicity model is unique up to associates. -/
theorem scaledMultiplicity_associated {p q : k[X]} {n m : ℕ}
    (hp : Prime p) (hq : Prime q) (hn : 0 < n) (hm : 0 < m)
    (h : ∀ f : k[X], f ≠ 0 → scaledMultiplicity p n f = scaledMultiplicity q m f) :
    Associated p q := sorry

end Polynomial
