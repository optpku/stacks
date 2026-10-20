/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Kummer--Artin--Schreier quotient polynomials

For a prime cyclotomic root `ζ`, the change of variables `Y = 1 + (1 - ζ) X` produces a
normalized quotient polynomial.  The data and its functorial properties are kept separate from
the cancellation needed for the exact addition formula: over a ring with zero divisors the
multiplied formula is the canonical unconditional statement.

@stack 09F2
@stack 09F3
-/

open scoped BigOperators
open Polynomial

universe u v

namespace KummerArtinSchreier

section Law

variable {A : Type u} [Add A] [Mul A]

/-- The scaled multiplicative law `x + y + w * x * y`. -/
@[stacks 09F2 "scaled multiplicative law"]
def mulLaw (w x y : A) : A :=
  x + y + w * x * y

end Law

section Semiring

variable {A : Type u} [Semiring A]

/-- The partial geometric sum `1 + ζ + ... + ζ ^ (j - 1)`. -/
@[stacks 09F2 "partial sums for the one-sub quotient polynomial"]
def partialSum (ζ : A) (j : ℕ) : A :=
  ∑ m ∈ Finset.range j, ζ ^ m

/-- The empty partial geometric sum vanishes. -/
@[simp, stacks 09F2 "zero partial sum"]
theorem partialSum_zero (ζ : A) : partialSum ζ 0 = 0 := sorry
-- Proof strategy: unfold `partialSum`; both `Finset.range 0` and its sum are empty.

/-- A partial geometric sum is extended by its last power. -/
@[stacks 09F2 "successor partial sum"]
theorem partialSum_succ (ζ : A) (j : ℕ) :
    partialSum ζ (j + 1) = partialSum ζ j + ζ ^ j := sorry
-- Proof strategy: unfold `partialSum` and apply `Finset.sum_range_succ`.

/-- Partial geometric sums split at an arbitrary index. -/
@[stacks 09F2 "addition law for partial sums"]
theorem partialSum_add (ζ : A) (i j : ℕ) :
    partialSum ζ (i + j) = partialSum ζ i + ζ ^ i * partialSum ζ j := sorry
-- Proof strategy: split `Finset.range (i + j)` at `i`, reindex the tail by `m ↦ i + m`, and use
-- `pow_add` before factoring out `ζ ^ i`.

/-- Semiring homomorphisms preserve the partial geometric sums. -/
@[simp, stacks 09F2 "base change of partial sums for the quotient polynomial"]
theorem map_partialSum {B : Type v} [Semiring B] (f : A →+* B) (ζ : A) (j : ℕ) :
    f (partialSum ζ j) = partialSum (f ζ) j := sorry
-- Proof strategy: unfold `partialSum`, commute `f` with the finite sum, and rewrite each power by
-- `map_pow`.

end Semiring

section CommSemiring

variable {A : Type u} [CommSemiring A]

/-- The canonical product whose roots are the negatives of the partial sums of powers of `ζ`. -/
@[stacks 09F2 "canonical one-sub quotient polynomial"]
noncomputable def polynomial (p : ℕ) (ζ : A) : A[X] :=
  ∏ j ∈ Finset.range p, (X + C (partialSum ζ j))

/-- The scaled multiplicative law is carried to multiplication by `x ↦ 1 + w * x`. -/
@[stacks 09F2 "scaled multiplicative law comparison"]
theorem one_add_mulLaw (w x y : A) :
    1 + w * mulLaw w x y = (1 + w * x) * (1 + w * y) := sorry
-- Proof strategy: unfold `mulLaw` and normalize with commutative semiring distributivity.

/-- The canonical quotient polynomial commutes with base change. -/
@[simp, stacks 09F2 "base change of the canonical quotient polynomial"]
theorem map_polynomial {B : Type v} [CommSemiring B] (f : A →+* B) (p : ℕ) (ζ : A) :
    (polynomial p ζ).map f = polynomial p (f ζ) := sorry
-- Proof strategy: unfold `polynomial`, map the finite product and each translated linear factor,
-- and use `map_partialSum`.

/-- The canonical quotient polynomial at index zero is `1`. -/
@[simp, stacks 09F2 "zero-index canonical quotient polynomial"]
theorem polynomial_zero (ζ : A) : polynomial 0 ζ = 1 := sorry
-- Proof strategy: unfold `polynomial`; the indexed product over `Finset.range 0` is empty.

/-- Adding one index appends the corresponding translated linear factor. -/
@[stacks 09F2 "successor canonical quotient polynomial"]
theorem polynomial_succ (p : ℕ) (ζ : A) :
    polynomial (p + 1) ζ = polynomial p ζ * (X + C (partialSum ζ p)) := sorry
-- Proof strategy: unfold `polynomial` and apply `Finset.prod_range_succ`.

/-- The canonical quotient polynomial is monic. -/
@[stacks 09F2 "monicity of the canonical quotient polynomial"]
theorem polynomial_monic (p : ℕ) (ζ : A) : (polynomial p ζ).Monic := sorry
-- Proof strategy: each factor `X + C (partialSum ζ j)` is monic; apply monicity of finite
-- products.

/-- The canonical quotient polynomial has degree equal to its index in a nontrivial semiring. -/
@[stacks 09F2 "degree of the canonical quotient polynomial"]
theorem polynomial_natDegree [Nontrivial A] (p : ℕ) (ζ : A) :
    (polynomial p ζ).natDegree = p := sorry
-- Proof strategy: use `polynomial_monic` to add natDegrees through the product; every translated
-- linear factor has natDegree one, so the range product has degree `p`.

end CommSemiring

section Ring

variable {A : Type u} [Ring A]

/-- The standard telescoping form of the geometric-sum identity. -/
@[stacks 09F2 "geometric-sum factorization"]
theorem one_sub_mul_partialSum (ζ : A) (j : ℕ) :
    (1 - ζ) * partialSum ζ j = 1 - ζ ^ j := sorry
-- Proof strategy: unfold `partialSum` and use the finite geometric-series telescoping identity;
-- alternatively induct on `j` with `partialSum_succ` and `pow_succ`.

/-- The partial geometric sum satisfies the standard telescoping identity. -/
@[stacks 09F2 "telescoping partial sum identity"]
theorem one_sub_mul_partialSum_eq_pow (ζ : A) (j : ℕ) :
    1 - (1 - ζ) * partialSum ζ j = ζ ^ j := sorry
-- Proof strategy: rewrite with `one_sub_mul_partialSum` and simplify the double subtraction.

/-- The coefficient of the correction to `X ^ p - X` in degree `i`. -/
@[stacks 09F2 "canonical correction coefficient"]
noncomputable def correctionCoeff (p : ℕ) (P : A[X]) (i : ℕ) : A :=
  (P - (X ^ p - X)).coeff i

end Ring

section CommRing

variable {A : Type u} [CommRing A]

/-- A polynomial has the normalized source shape when its only corrections to `X ^ p - X`
occur in the interior degrees and those corrections lie in `(1 - ζ)`. -/
@[stacks 09F2 "normalized shape of the one-sub quotient polynomial"]
def HasShape (p : ℕ) (ζ : A) (P : A[X]) : Prop :=
  (∀ i, 0 < i → i < p →
      correctionCoeff p P i ∈ Ideal.span ({1 - ζ} : Set A)) ∧
    P = X ^ p - X +
      ∑ i ∈ Finset.Icc 1 (p - 1), C (correctionCoeff p P i) * X ^ i

/-- The quotient identity obtained from the substitution `Y = 1 + (1 - ζ) X`. -/
@[stacks 09F2 "one-sub quotient identity"]
def HasQuotientIdentity (p : ℕ) (ζ : A) (P : A[X]) : Prop :=
  C ((1 - ζ) ^ p) * P = (C (1 : A) + C (1 - ζ) * X) ^ p - 1

/-- A normalized quotient polynomial attached to the distinguished element `1 - ζ`. -/
@[stacks 09F2 "one-sub quotient polynomial"]
def IsQuotient (p : ℕ) (ζ : A) (P : A[X]) : Prop :=
  HasShape p ζ P ∧ HasQuotientIdentity p ζ P

/-- Each translated partial sum is a root of the canonical quotient polynomial. -/
@[stacks 09F2 "translated partial sum root"]
theorem eval_polynomial_neg_partialSum {p : ℕ} (ζ : A) {j : ℕ} (hj : j < p) :
    (polynomial p ζ).eval (-partialSum ζ j) = 0 := sorry
-- Proof strategy: unfold the product defining `polynomial`; the factor indexed by `j` belongs to
-- `Finset.range p` by `hj` and evaluates to zero.

/-- Each negative partial sum is a root of the canonical quotient polynomial. -/
@[stacks 09F2 "translated partial sum root predicate"]
theorem isRoot_polynomial_neg_partialSum {p : ℕ} (ζ : A) {j : ℕ} (hj : j < p) :
    IsRoot (polynomial p ζ) (-partialSum ζ j) := sorry
-- Proof strategy: unfold `IsRoot` and apply `eval_polynomial_neg_partialSum ζ hj`.

end CommRing

namespace HasShape

variable {A : Type u} [CommRing A] {p : ℕ} {ζ : A} {P : A[X]}

/-- A normalized shape exposes membership of every interior correction coefficient. -/
@[stacks 09F2 "normalized-shape coefficient membership"]
theorem correctionCoeff_mem (hP : HasShape p ζ P) {i : ℕ} (hi : 0 < i) (hip : i < p) :
    correctionCoeff p P i ∈ Ideal.span ({1 - ζ} : Set A) := sorry
-- Proof strategy: project the first component of `hP` and specialize it to `i`, `hi`, and `hip`.

/-- A normalized shape exposes its canonical displayed polynomial equality. -/
@[stacks 09F2 "normalized-shape polynomial equality"]
theorem eq (hP : HasShape p ζ P) :
    P = X ^ p - X +
      ∑ i ∈ Finset.Icc 1 (p - 1), C (correctionCoeff p P i) * X ^ i := sorry
-- Proof strategy: project the displayed equality from the second component of `hP`.

/-- Normalized polynomial shape is preserved by arbitrary base change. -/
@[stacks 09F2 "base change of normalized polynomial shape"]
theorem map {B : Type v} [CommRing B] (hP : HasShape p ζ P) (f : A →+* B) :
    HasShape p (f ζ) (P.map f) := sorry
-- Proof strategy: map `hP.eq` coefficientwise, use `map_sub`, `map_X`, `map_C`, and finite-sum
-- compatibility, and identify mapped correction coefficients.  Map the principal-ideal witnesses
-- from `hP.correctionCoeff_mem` to prove the interior membership clauses.

end HasShape

namespace HasQuotientIdentity

variable {A : Type u} [CommRing A] {p : ℕ} {ζ : A} {P : A[X]}

/-- A quotient identity exposes its defining polynomial equality. -/
@[stacks 09F2 "one-sub quotient identity specification"]
theorem eq (hP : HasQuotientIdentity p ζ P) :
    C ((1 - ζ) ^ p) * P = (C (1 : A) + C (1 - ζ) * X) ^ p - 1 := sorry
-- Proof strategy: unfold `HasQuotientIdentity`; this is its defining equality.

/-- The quotient identity is preserved by arbitrary base change. -/
@[stacks 09F2 "base change of the one-sub quotient identity"]
theorem map {B : Type v} [CommRing B] (hP : HasQuotientIdentity p ζ P) (f : A →+* B) :
    HasQuotientIdentity p (f ζ) (P.map f) := sorry
-- Proof strategy: map `hP.eq` through `Polynomial.map f` and normalize `map_C`, `map_X`, powers,
-- subtraction, and multiplication.

/-- A quotient identity determines the canonical polynomial when `1 - ζ` is regular. -/
@[stacks 09F2 "uniqueness from the one-sub quotient identity"]
theorem eq_polynomial [Fact p.Prime]
    (hP : HasQuotientIdentity p ζ P) (hζ : IsRoot (cyclotomic p A) ζ)
    (h_regular : IsRegular (1 - ζ)) : P = polynomial p ζ := sorry
-- Proof strategy: prove the same quotient identity for the explicit product `polynomial p ζ`
-- using the prime cyclotomic relation.  Subtract the two identities and cancel
-- `C ((1 - ζ) ^ p)`, which is regular in `A[X]` by `h_regular`, to obtain equality.

/-- The quotient identity gives the addition formula after multiplication by `(1 - ζ) ^ p`,
without any cancellation hypothesis. -/
@[stacks 09F2 "multiplied one-sub addition formula"]
theorem addFormula_mul {B : Type v} [CommSemiring B] [Algebra A B]
    (hP : HasQuotientIdentity p ζ P) (x y : B) :
    algebraMap A B (1 - ζ) ^ p *
        aeval (mulLaw (algebraMap A B (1 - ζ)) x y) P =
      algebraMap A B (1 - ζ) ^ p *
        (aeval x P + aeval y P +
          algebraMap A B (1 - ζ) ^ p * aeval x P * aeval y P) := sorry
-- Proof strategy: evaluate `hP.eq` at `mulLaw (algebraMap A B (1 - ζ)) x y`, rewrite
-- `one_add_mulLaw`, and expand the resulting product.  Substitute the two evaluations of
-- `hP.eq` at `x` and `y`, then normalize without cancelling the common scalar factor.

/-- Regularity of `1 - ζ` cancels the common factor in the universal addition identity. -/
@[stacks 09F2 "one-sub addition formula under regularity"]
theorem addFormula_of_isRegular {B : Type v} [CommSemiring B] [Algebra A B]
    (hP : HasQuotientIdentity p ζ P) (h_regular : IsRegular (1 - ζ)) (x y : B) :
    aeval (mulLaw (algebraMap A B (1 - ζ)) x y) P =
      aeval x P + aeval y P +
        algebraMap A B (1 - ζ) ^ p * aeval x P * aeval y P := sorry
-- Proof strategy: first prove the corresponding polynomial identity universally over `A`, using
-- `addFormula_mul` and cancellation by the regular element `(1 - ζ) ^ p` in the source ring.
-- Base-change that identity to `B` and evaluate at `x` and `y`; do not assume that regularity is
-- preserved by the arbitrary algebra map `A →+* B`.

end HasQuotientIdentity

namespace IsQuotient

variable {A : Type u} [CommRing A] {p : ℕ} {ζ : A} {P : A[X]}

/-- A quotient polynomial has the canonical normalized coefficient shape. -/
@[stacks 09F2 "one-sub quotient polynomial shape"]
theorem hasShape (hP : IsQuotient p ζ P) : HasShape p ζ P := sorry
-- Proof strategy: unfold `IsQuotient` and project its first component.

/-- A quotient polynomial has the defining one-sub quotient identity. -/
@[stacks 09F2 "one-sub quotient polynomial identity owner"]
theorem hasQuotientIdentity (hP : IsQuotient p ζ P) : HasQuotientIdentity p ζ P := sorry
-- Proof strategy: unfold `IsQuotient` and project its second component.

/-- Every interior correction coefficient of a quotient polynomial lies in `(1 - ζ)`. -/
@[stacks 09F2 "one-sub quotient polynomial coefficient membership"]
theorem correctionCoeff_mem (hP : IsQuotient p ζ P) {i : ℕ} (hi : 0 < i) (hip : i < p) :
    correctionCoeff p P i ∈ Ideal.span ({1 - ζ} : Set A) := sorry
-- Proof strategy: apply `hP.hasShape.correctionCoeff_mem hi hip`.

/-- The defining quotient identity of a quotient polynomial. -/
@[stacks 09F2 "one-sub quotient polynomial identity"]
theorem quotient_eq (hP : IsQuotient p ζ P) :
    C ((1 - ζ) ^ p) * P = (C (1 : A) + C (1 - ζ) * X) ^ p - 1 := sorry
-- Proof strategy: apply `hP.hasQuotientIdentity.eq`.

/-- The canonical correction coefficients give the displayed source polynomial. -/
@[stacks 09F2 "one-sub quotient polynomial displayed shape"]
theorem shape_eq (hP : IsQuotient p ζ P) :
    P = X ^ p - X +
      ∑ i ∈ Finset.Icc 1 (p - 1), C (correctionCoeff p P i) * X ^ i := sorry
-- Proof strategy: apply `hP.hasShape.eq`.

/-- A quotient polynomial admits the existential coefficient presentation used by the source
statement. -/
@[stacks 09F2 "one-sub quotient polynomial source shape"]
theorem exists_shape (hP : IsQuotient p ζ P) :
    ∃ a : ℕ → A,
      P = X ^ p - X + ∑ i ∈ Finset.Icc 1 (p - 1), C (a i) * X ^ i := sorry
-- Proof strategy: choose `a := correctionCoeff p P` and use `hP.shape_eq`.

/-- The canonical coefficients recover the existential coefficient presentation used in the
source statement. -/
@[stacks 09F2 "one-sub quotient polynomial coefficient presentation"]
theorem exists_coefficients (hP : IsQuotient p ζ P) :
    ∃ a : ℕ → A,
      (∀ i, 0 < i → i < p → a i ∈ Ideal.span ({1 - ζ} : Set A)) ∧
        P = X ^ p - X + ∑ i ∈ Finset.Icc 1 (p - 1), C (a i) * X ^ i ∧
        C ((1 - ζ) ^ p) * P = (C (1 : A) + C (1 - ζ) * X) ^ p - 1 := sorry
-- Proof strategy: choose `a := correctionCoeff p P`; combine `hP.correctionCoeff_mem`,
-- `hP.shape_eq`, and `hP.quotient_eq`.

/-- Evaluating a quotient polynomial separates its `X ^ p - X` term from the canonical
correction sum. -/
@[stacks 09F6 "evaluation of the quotient-polynomial correction"]
theorem aeval_sub_eq_sum {B : Type v} [CommRing B] [Algebra A B]
    (hP : IsQuotient p ζ P) (z : B) :
    aeval z P - (z ^ p - z) =
      ∑ i ∈ Finset.Icc 1 (p - 1),
        algebraMap A B (correctionCoeff p P i) * z ^ i := sorry
-- Proof strategy: evaluate `hP.shape_eq` at `z`, commute `aeval` with the finite sum, and simplify
-- `aeval z (X ^ p - X)`, `aeval z (C a * X ^ i)`, and the final subtraction.

/-- Quotient polynomials are preserved by arbitrary homomorphisms of commutative rings. -/
@[stacks 09F2 "base change of one-sub quotient polynomials"]
theorem map {B : Type v} [CommRing B] (hP : IsQuotient p ζ P) (f : A →+* B) :
    IsQuotient p (f ζ) (P.map f) := sorry
-- Proof strategy: unfold `IsQuotient` and combine `hP.hasShape.map f` with
-- `hP.hasQuotientIdentity.map f`.

end IsQuotient

section Canonical

variable {A : Type u} [CommRing A] {p : ℕ} {ζ : A}

/-- Under a prime cyclotomic relation, the canonical polynomial reduces modulo `(1 - ζ)` to
`X ^ p - X`. -/
@[stacks 09F2 "canonical quotient polynomial modulo one minus the root"]
theorem map_polynomial_quotient_eq
    [Fact p.Prime]
    (hζ : IsRoot (cyclotomic p A) ζ) :
    (polynomial p ζ).map (Ideal.Quotient.mk (Ideal.span ({1 - ζ} : Set A))) =
      (X ^ p - X : (A ⧸ Ideal.span ({1 - ζ} : Set A))[X]) := sorry
-- Proof strategy: use `map_polynomial`; in the quotient, `ζ = 1`, so every partial sum maps to the
-- corresponding natural number.  Rewrite the product as `∏ j < p, (X + C j)` and apply the
-- prime-characteristic identity `∏ j : ZMod p, (X - C j) = X ^ p - X`, transporting indices and
-- signs as needed.

/-- Every interior correction coefficient of the canonical polynomial lies in `(1 - ζ)`. -/
@[stacks 09F2 "canonical quotient polynomial coefficient membership"]
theorem correctionCoeff_polynomial_mem
    [Fact p.Prime]
    (hζ : IsRoot (cyclotomic p A) ζ) {i : ℕ} (hi : 0 < i) (hip : i < p) :
    correctionCoeff p (polynomial p ζ) i ∈ Ideal.span ({1 - ζ} : Set A) := sorry
-- Proof strategy: take the degree-`i` coefficient of `map_polynomial_quotient_eq hζ`.  Rewrite
-- coefficients of a mapped polynomial through the quotient map; the coefficient of
-- `X ^ p - X` vanishes for `0 < i < p`, so the correction coefficient lies in the quotient-map
-- kernel, namely `Ideal.span ({1 - ζ} : Set A)`.

end Canonical

namespace IsQuotient

variable {A : Type u} [CommRing A] {p : ℕ} {ζ : A} {P : A[X]}

/-- A quotient polynomial is the canonical one whenever its quotient identity can be cancelled by
the regular element `1 - ζ`. -/
@[stacks 09F2 "uniqueness of the one-sub quotient polynomial"]
theorem eq_polynomial
    [Fact p.Prime]
    (hP : IsQuotient p ζ P) (hζ : IsRoot (cyclotomic p A) ζ)
    (h_regular : IsRegular (1 - ζ)) : P = polynomial p ζ := sorry
-- Proof strategy: apply `hP.hasQuotientIdentity.eq_polynomial hζ h_regular`.

/-- In a domain, a primitive root of prime order supplies the regularity needed for the exact
addition formula. -/
@[stacks 09F2 "one-sub addition formula for a primitive root in a domain"]
theorem addFormula_of_isPrimitiveRoot [IsDomain A] [Fact p.Prime]
    (hP : IsQuotient p ζ P) (hζ : IsPrimitiveRoot ζ p)
    {B : Type v} [CommSemiring B] [Algebra A B] (x y : B) :
    aeval (mulLaw (algebraMap A B (1 - ζ)) x y) P =
      aeval x P + aeval y P +
        algebraMap A B (1 - ζ) ^ p * aeval x P * aeval y P := sorry
-- Proof strategy: in a domain, primitivity and primality give `ζ ≠ 1`, hence `1 - ζ ≠ 0` and
-- `IsRegular (1 - ζ)`.  Apply `hP.hasQuotientIdentity.addFormula_of_isRegular` with that regularity
-- witness.

end IsQuotient

section Existence

variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime] {ζ : A}

/-- A root of the prime cyclotomic polynomial gives the canonical quotient polynomial.  This is
the base-change-stable hypothesis needed over rings with zero divisors. -/
@[stacks 09F2 "canonical quotient polynomial from a cyclotomic root"]
theorem polynomial_spec
    (hζ : IsRoot (cyclotomic p A) ζ) :
    IsQuotient p ζ (polynomial p ζ) := sorry
-- Proof strategy: prove `HasShape` using `correctionCoeff_polynomial_mem hζ` and the coefficientwise
-- reconstruction of the monic degree-`p` polynomial.  Prove `HasQuotientIdentity` by multiplying
-- the explicit product by `C ((1 - ζ) ^ p)`, applying `one_sub_mul_partialSum_eq_pow` factorwise,
-- and using the prime cyclotomic relation to identify the product with the binomial difference.

/-- The cyclotomic relation makes the canonical quotient polynomial an exact homomorphism from
the scaled multiplicative law to its degree-`p` deformation. -/
@[stacks 09F2 "exact addition formula for the canonical quotient polynomial"]
theorem addFormula
    (hζ : IsRoot (cyclotomic p A) ζ)
    {B : Type v} [CommSemiring B] [Algebra A B] (x y : B) :
    aeval (mulLaw (algebraMap A B (1 - ζ)) x y) (polynomial p ζ) =
      aeval x (polynomial p ζ) + aeval y (polynomial p ζ) +
        algebraMap A B (1 - ζ) ^ p *
          aeval x (polynomial p ζ) * aeval y (polynomial p ζ) := sorry
-- Proof strategy: expand the explicit product at the three arguments and use `partialSum_add`
-- together with `one_add_mulLaw` to match factors under the cyclic index translation.  This direct
-- canonical-polynomial proof works after arbitrary base change and does not cancel `1 - ζ` in `B`.

/-- Existence of a quotient polynomial from a root of the prime cyclotomic polynomial. -/
@[stacks 09F2 "existence of a quotient polynomial from a cyclotomic root"]
theorem exists_of_isRoot
    (hζ : IsRoot (cyclotomic p A) ζ) :
    ∃ P : A[X], IsQuotient p ζ P := sorry
-- Proof strategy: choose `P := polynomial p ζ` and apply `polynomial_spec hζ`.

/-- A primitive root together with regularity of `1 - ζ` satisfies the prime cyclotomic
relation, even when the ambient ring has zero divisors. -/
@[stacks 09F2 "cyclotomic relation from a regular primitive root"]
theorem isRoot_of_isPrimitiveRoot
    (hζ : IsPrimitiveRoot ζ p) (h_regular : IsRegular (1 - ζ)) :
    IsRoot (cyclotomic p A) ζ := sorry
-- Proof strategy: use the factorization of `X ^ p - 1` into prime cyclotomic factors and
-- `hζ.pow_eq_one`.  Primitivity rules out every proper-order factor; cancel the regular factor
-- arising from `1 - ζ` to isolate `cyclotomic p A` at `ζ`.

/-- Over a domain, Mathlib's primitive-root predicate implies the cyclotomic relation and hence
gives the canonical quotient polynomial. -/
@[stacks 09F2 "existence of a quotient polynomial from a primitive root"]
theorem exists_of_isPrimitiveRoot [IsDomain A]
    (hζ : IsPrimitiveRoot ζ p) :
    ∃ P : A[X], IsQuotient p ζ P := sorry
-- Proof strategy: derive `ζ ≠ 1` from primitivity and primality, hence regularity of `1 - ζ` in the
-- domain.  Apply `isRoot_of_isPrimitiveRoot hζ`, then `exists_of_isRoot`.

/-- Over a domain, the canonical quotient polynomial attached to a primitive root satisfies the
exact addition formula. -/
@[stacks 09F2 "exact addition formula from a primitive root in a domain"]
theorem addFormula_of_isPrimitiveRoot [IsDomain A]
    (hζ : IsPrimitiveRoot ζ p)
    {B : Type v} [CommSemiring B] [Algebra A B] (x y : B) :
    aeval (mulLaw (algebraMap A B (1 - ζ)) x y) (polynomial p ζ) =
      aeval x (polynomial p ζ) + aeval y (polynomial p ζ) +
        algebraMap A B (1 - ζ) ^ p *
          aeval x (polynomial p ζ) * aeval y (polynomial p ζ) := sorry
-- Proof strategy: obtain the cyclotomic root relation exactly as in `exists_of_isPrimitiveRoot`
-- and apply the canonical `addFormula` theorem.

end Existence

section RootPresentationAPI

universe uA uK uL

variable {A : Type uA} [CommRing A]
variable {K : Type uK} [Field K] [Algebra A K]
variable {L : Type uL} [Field L] [Algebra K L]
variable {p : ℕ}

/-- A Kummer--Artin--Schreier root equation over a coefficient ring `A`, an intermediate field `K`,
and an ambient field `L`.  The generator condition is deliberately separate so the equation can be
reused for subextensions and for later adjoining arguments. -/
@[stacks 09F3 "Kummer root equation presentation"]
structure RootEquation
    (A : Type uA) [CommRing A]
    (K : Type uK) [Field K] [Algebra A K]
    (L : Type uL) [Field L] [Algebra K L]
    (p : ℕ) where
  /-- The distinguished primitive `p`th root of unity in the coefficient ring. -/
  ζ : A
  /-- The quotient polynomial attached to `ζ`. -/
  P : A[X]
  /-- The right-hand side of the root equation in the intermediate field. -/
  ξ : K
  /-- The chosen root in the ambient field. -/
  z : L
  /-- The distinguished element is a primitive `p`th root of unity. -/
  isPrimitiveRoot : IsPrimitiveRoot ζ p
  /-- The polynomial has the canonical one-sub quotient shape. -/
  isQuotient : IsQuotient p ζ P
  /-- The chosen root satisfies `P(z) = ξ` after base change to `L`. -/
  eval_eq : aeval z (P.map (algebraMap A K)) = algebraMap K L ξ

/-- A Kummer--Artin--Schreier root presentation whose chosen root generates the ambient field. -/
@[stacks 09F3 "Kummer root presentation with a generator"]
structure RootPresentation
    (A : Type uA) [CommRing A]
    (K : Type uK) [Field K] [Algebra A K]
    (L : Type uL) [Field L] [Algebra K L]
    (p : ℕ) extends RootEquation A K L p where
  /-- The chosen root generates the ambient extension over `K`. -/
  adjoin_eq_top : Algebra.adjoin K ({toRootEquation.z} : Set L) = ⊤

namespace RootEquation

/-- The quotient-polynomial condition carried by a root equation. -/
@[stacks 09F3 "root equation quotient condition"]
theorem quotient (h : RootEquation A K L p) : IsQuotient p h.ζ h.P := sorry
-- Proof strategy: return the structure field `h.isQuotient`.

/-- The evaluation equation carried by a root equation. -/
@[stacks 09F3 "root equation evaluation condition"]
theorem eval (h : RootEquation A K L p) :
    aeval h.z (h.P.map (algebraMap A K)) = algebraMap K L h.ξ := sorry
-- Proof strategy: return the structure field `h.eval_eq`.

end RootEquation

namespace RootPresentation

/-- The underlying root equation of a generating presentation. -/
@[stacks 09F3 "underlying Kummer root equation"]
abbrev equation (h : RootPresentation A K L p) : RootEquation A K L p := h.toRootEquation

/-- Package a root equation together with the assertion that its chosen root generates the ambient
field.  This is the canonical constructor used by source-facing lemmas that start from separate
polynomial, evaluation, and generation hypotheses. -/
@[stacks 09F3 "root presentation from an equation and generation"]
def ofEquation (h : RootEquation A K L p)
    (hgen : Algebra.adjoin K ({h.z} : Set L) = ⊤) : RootPresentation A K L p :=
  { h with adjoin_eq_top := hgen }

/-- A generating presentation exposes its quotient-polynomial condition. -/
@[stacks 09F3 "root presentation quotient condition"]
theorem quotient (h : RootPresentation A K L p) : IsQuotient p h.ζ h.P := sorry
-- Proof strategy: apply `RootEquation.quotient h.toRootEquation`.

/-- A generating presentation exposes its root equation. -/
@[stacks 09F3 "root presentation evaluation condition"]
theorem eval (h : RootPresentation A K L p) :
    aeval h.z (h.P.map (algebraMap A K)) = algebraMap K L h.ξ := sorry
-- Proof strategy: apply `RootEquation.eval h.toRootEquation`.

/-- A generating presentation exposes the field-generation condition. -/
@[stacks 09F3 "root presentation generation condition"]
theorem adjoin (h : RootPresentation A K L p) :
    Algebra.adjoin K ({h.z} : Set L) = ⊤ := sorry
-- Proof strategy: return the structure field `h.adjoin_eq_top`.

end RootPresentation

end RootPresentationAPI

end KummerArtinSchreier
