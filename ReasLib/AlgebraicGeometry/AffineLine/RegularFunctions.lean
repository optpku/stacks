module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import ReasLib.AlgebraicGeometry.AffineSpace.RegularFunctions

/-!
# Classical regular functions on the affine line

Regular functions on a Zariski locally closed subset of the k-points of the affine line,
in the classical sense.
-/

@[expose] public section

noncomputable section

universe u

namespace Polynomial

variable {k : Type u} [Field k]

/-- A subset of the affine line is Zariski locally closed when it is the difference of
zero loci of nested ideals. -/
def IsZariskiLocallyClosed (Z : Set k) : Prop :=
  ∃ I J : Ideal (Polynomial k), I ≤ J ∧
    Z = {x | ∀ p ∈ I, p.eval x = 0} \ {x | ∀ p ∈ J, p.eval x = 0}

/-- Zariski locally closed subsets of the affine line are differences of nested zero loci. -/
theorem isZariskiLocallyClosed_iff (Z : Set k) :
    IsZariskiLocallyClosed Z ↔
      ∃ I J : Ideal (Polynomial k), I ≤ J ∧
        Z = {x | ∀ p ∈ I, p.eval x = 0} \ {x | ∀ p ∈ J, p.eval x = 0} :=
  sorry

/-- The affine line is Zariski locally closed in itself. -/
theorem isZariskiLocallyClosed_univ : IsZariskiLocallyClosed (Set.univ : Set k) :=
  sorry

/-- A relative Zariski open of `Z ⊆ k` is the complement in `Z` of a zero locus. -/
def IsZariskiOpenIn (U Z : Set k) : Prop :=
  U ⊆ Z ∧ ∃ I : Ideal (Polynomial k), U = Z \ {x | ∀ p ∈ I, p.eval x = 0}

/-- Relative Zariski opens on the affine line are complements of zero loci inside `Z`. -/
theorem isZariskiOpenIn_iff (U Z : Set k) :
    IsZariskiOpenIn U Z ↔
      U ⊆ Z ∧ ∃ I : Ideal (Polynomial k), U = Z \ {x | ∀ p ∈ I, p.eval x = 0} :=
  sorry

/-- A function on a subset of the affine line is regular if it is Zariski-locally a ratio of
polynomials with nonvanishing denominator. -/
def IsRegular {Z : Set k} (φ : Z → k) : Prop :=
  ∀ z : Z, ∃ U : Set k, IsZariskiOpenIn U Z ∧ z.val ∈ U ∧
    ∃ f g : Polynomial k,
      (∀ u ∈ U, g.eval u ≠ 0) ∧
      (∀ u : Z, u.val ∈ U → φ u = f.eval u.val / g.eval u.val)

/-- Regularity on the affine line is the existence of local polynomial ratios. -/
theorem isRegular_iff {Z : Set k} (φ : Z → k) :
    IsRegular φ ↔
      ∀ z : Z, ∃ U : Set k, IsZariskiOpenIn U Z ∧ z.val ∈ U ∧
        ∃ f g : Polynomial k,
          (∀ u ∈ U, g.eval u ≠ 0) ∧
          (∀ u : Z, u.val ∈ U → φ u = f.eval u.val / g.eval u.val) :=
  sorry

/-- A function on a subset of the affine line is polynomial if it is given by evaluation of a
univariate polynomial. -/
def IsPolynomial {Z : Set k} (φ : Z → k) : Prop :=
  ∃ p : Polynomial k, ∀ z : Z, φ z = p.eval z.val

/-- Polynomial functions on the affine line are those given by a univariate polynomial. -/
theorem isPolynomial_iff {Z : Set k} (φ : Z → k) :
    IsPolynomial φ ↔ ∃ p : Polynomial k, ∀ z : Z, φ z = p.eval z.val :=
  sorry

/-- Polynomial functions on the affine line are regular. -/
theorem isRegular_of_isPolynomial {Z : Set k} {φ : Z → k}
    (hφ : IsPolynomial φ) : IsRegular φ :=
  sorry

/-- Regular functions are closed under pointwise addition. -/
theorem isRegular_add {Z : Set k} {φ ψ : Z → k}
    (hφ : IsRegular φ) (hψ : IsRegular ψ) : IsRegular (φ + ψ) :=
  sorry

/-- Regular functions are closed under pointwise multiplication. -/
theorem isRegular_mul {Z : Set k} {φ ψ : Z → k}
    (hφ : IsRegular φ) (hψ : IsRegular ψ) : IsRegular (φ * ψ) :=
  sorry

/-- Constant functions on the affine line are regular. -/
theorem isRegular_const {Z : Set k} (c : k) :
    IsRegular (algebraMap k (Z → k) c) :=
  sorry

/-- The algebra of regular functions on a subset of the affine line. -/
def regularFunctions (Z : Set k) : Subalgebra k (Z → k) where
  carrier := {φ | IsRegular φ}
  add_mem' := isRegular_add
  mul_mem' := isRegular_mul
  algebraMap_mem' := isRegular_const

/-- Membership in `regularFunctions Z` on the affine line is regularity. -/
theorem mem_regularFunctions_iff {Z : Set k} {φ : Z → k} :
    φ ∈ regularFunctions Z ↔ IsRegular φ :=
  sorry

/-- Regularity on the affine line agrees with multivariate regularity in one variable. -/
theorem isRegular_univ_iff_mvPolynomial (φ : k → k) :
    IsRegular (fun z : (Set.univ : Set k) ↦ φ z.val) ↔
      MvPolynomial.IsRegular
        (fun z : (Set.univ : Set (Fin 1 → k)) ↦ φ (z.val 0)) :=
  sorry

/-- Polynomiality on the affine line agrees with multivariate polynomiality in one variable. -/
theorem isPolynomial_univ_iff_mvPolynomial (φ : k → k) :
    IsPolynomial (fun z : (Set.univ : Set k) ↦ φ z.val) ↔
      MvPolynomial.IsPolynomial
        (fun z : (Set.univ : Set (Fin 1 → k)) ↦ φ (z.val 0)) :=
  sorry

/-- The function `x ↦ (1 + x ^ 2)⁻¹` on the real line. -/
def invOneAddSq : ℝ → ℝ := fun x ↦ (1 + x ^ 2)⁻¹

/-- The reciprocal of `1 + x ^ 2` is regular on the real affine line but not polynomial. -/
theorem isRegular_not_isPolynomial_invOneAddSq :
    IsRegular (fun z : (Set.univ : Set ℝ) ↦ invOneAddSq z.val) ∧
      ¬ IsPolynomial (fun z : (Set.univ : Set ℝ) ↦ invOneAddSq z.val) :=
  sorry

/-- The function `x ↦ (x ^ 2 - p)⁻¹` on the `p`-adic numbers. -/
def invXSqSubNat (p : ℕ) [Fact p.Prime] : ℚ_[p] → ℚ_[p] :=
  fun x ↦ (x ^ 2 - (p : ℚ_[p]))⁻¹

/-- The reciprocal of `x ^ 2 - p` is regular on the p-adic affine line but not polynomial. -/
theorem isRegular_not_isPolynomial_invXSqSubNat (p : ℕ) [Fact p.Prime] :
    IsRegular (fun z : (Set.univ : Set ℚ_[p]) ↦ invXSqSubNat p z.val) ∧
      ¬ IsPolynomial (fun z : (Set.univ : Set ℚ_[p]) ↦ invXSqSubNat p z.val) :=
  sorry

end Polynomial
