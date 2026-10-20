/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.MvPolynomial.Fin
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite-Variable Homogenization

This leaf owns the standard affine chart of a polynomial ring in `Fin (n + 1)`
variables: the first variable is specialized to `1`, while the remaining
variables are reindexed by `Fin.succ`.  It also packages homogenization to a
chosen total degree and the formulas relating these two operations.

The API deliberately does not choose an ideal or a grading on a quotient.
Those applications belong to downstream geometry or commutative-algebra files.
-/

@[expose] public section

open scoped BigOperators

universe u

namespace MvPolynomial.Homogenization

variable {R : Type u}

section

variable [CommSemiring R]

/-- Tag `061R`: specialize the first variable of a finite multivariate
polynomial ring to `1` and reindex all successor variables. -/
@[stacks 061R "finite-variable dehomogenization"]
noncomputable def dehomogenize {n : ℕ} :
    MvPolynomial (Fin (n + 1)) R →ₐ[R] MvPolynomial (Fin n) R :=
  MvPolynomial.Fin.evalHead (A := R) 1 n

/-- Dehomogenization sends the distinguished first variable to `1`. -/
@[simp, stacks 061R "dehomogenization on first variable"]
theorem dehomogenize_X_zero {n : ℕ} :
    dehomogenize (R := R) (n := n) (MvPolynomial.X 0) = 1 := sorry

/-- Dehomogenization reindexes every successor variable to its affine
counterpart. -/
@[simp, stacks 061R "dehomogenization on successor variable"]
theorem dehomogenize_X_succ {n : ℕ} (i : Fin n) :
    dehomogenize (R := R) (n := n) (MvPolynomial.X i.succ) = MvPolynomial.X i := sorry

/-- Homogenization to a fixed total degree, bundled as an `R`-linear map. -/
@[stacks 061R "homogenization linear map"]
noncomputable def homogenizeToLM {n : ℕ} (d : ℕ) :
    MvPolynomial (Fin n) R →ₗ[R] MvPolynomial (Fin (n + 1)) R :=
  Finset.sum (Finset.range (d + 1)) fun i ↦
    (LinearMap.mulLeft R
      (MvPolynomial.X (0 : Fin (n + 1)) ^ (d - i))).comp
      ((MvPolynomial.rename (R := R) Fin.succ).toLinearMap.comp
        (MvPolynomial.homogeneousComponent (σ := Fin n) (R := R) i))

/-- Tag `061R`: homogenize a finite multivariate polynomial to total degree
`d` by inserting powers of the first variable into its homogeneous pieces.
Components above `d` are omitted, so applications normally assume
`p.totalDegree ≤ d`. -/
@[stacks 061R "finite-variable homogenization to a degree"]
noncomputable def homogenizeTo {n : ℕ} (d : ℕ) (p : MvPolynomial (Fin n) R) :
    MvPolynomial (Fin (n + 1)) R :=
  homogenizeToLM (R := R) d p

/-- Homogenization to any degree sends the zero polynomial to zero. -/
@[simp, stacks 061R "homogenization of zero"]
theorem homogenizeTo_zero {n : ℕ} (d : ℕ) :
    homogenizeTo (R := R) (n := n) d 0 = 0 := sorry

/-- Homogenization to a fixed degree is additive. -/
@[simp, stacks 061R "homogenization addition"]
theorem homogenizeTo_add {n : ℕ} (d : ℕ)
    (p q : MvPolynomial (Fin n) R) :
    homogenizeTo (R := R) d (p + q) =
      homogenizeTo (R := R) d p + homogenizeTo (R := R) d q := sorry

/-- Homogenization to a fixed degree commutes with `R`-scalar multiplication. -/
@[simp, stacks 061R "homogenization scalar multiplication"]
theorem homogenizeTo_smul {n : ℕ}
    (c : R) (p : MvPolynomial (Fin n) R) (d : ℕ) :
    homogenizeTo (R := R) d (c • p) = c • homogenizeTo (R := R) d p := sorry

/-- Applying `homogenizeToLM` is the original homogenization operation. -/
@[simp, stacks 061R "homogenization linear map application"]
theorem homogenizeToLM_apply {n : ℕ} (d : ℕ) (p : MvPolynomial (Fin n) R) :
    homogenizeToLM (R := R) d p = homogenizeTo (R := R) d p := sorry

/-- Homogenizing a degree-`d` homogeneous polynomial only reindexes its
variables. -/
@[stacks 061R "homogenization of a homogeneous polynomial"]
theorem homogenizeTo_of_isHomogeneous {n d : ℕ}
    {p : MvPolynomial (Fin n) R} (hp : p.IsHomogeneous d) :
    homogenizeTo (R := R) d p = MvPolynomial.rename Fin.succ p := sorry

/-- Homogenization of a coefficient constant is the corresponding power of
the first variable times that constant. -/
@[simp, stacks 061R "homogenization of a constant"]
theorem homogenizeTo_C {n : ℕ} (d : ℕ) (r : R) :
    homogenizeTo (R := R) (n := n) d (MvPolynomial.C r) =
      MvPolynomial.X (0 : Fin (n + 1)) ^ d * MvPolynomial.C r := sorry

/-- Homogenization to degree `d` is homogeneous of degree `d`. -/
@[stacks 061R "homogenization is homogeneous"]
theorem homogenizeTo_isHomogeneous {n : ℕ} (d : ℕ) (p : MvPolynomial (Fin n) R) :
    (homogenizeTo (R := R) d p).IsHomogeneous d := sorry

/-- Dehomogenization after the successor-variable rename is the identity. -/
@[simp, stacks 061R "dehomogenization after tail rename"]
theorem dehomogenize_rename_succ {n : ℕ} (p : MvPolynomial (Fin n) R) :
    dehomogenize (R := R) (n := n) (MvPolynomial.rename Fin.succ p) = p := sorry

/-- Dehomogenizing a homogenization recovers the original polynomial when the
chosen degree bounds its total degree. -/
@[stacks 061R "dehomogenization after homogenization"]
theorem dehomogenize_homogenizeTo {n : ℕ} (d : ℕ) (p : MvPolynomial (Fin n) R)
    (hp : p.totalDegree ≤ d) :
    dehomogenize (R := R) (n := n) (homogenizeTo (R := R) d p) = p := sorry

/-- Raising a permitted homogenization degree multiplies the minimal
homogenization by the corresponding first-variable power. -/
@[stacks 061R "homogenization degree shift"]
theorem homogenizeTo_eq_X_zero_pow_mul_totalDegree {n : ℕ} (d : ℕ)
    (p : MvPolynomial (Fin n) R) (hp : p.totalDegree ≤ d) :
    homogenizeTo (R := R) d p =
      MvPolynomial.X (0 : Fin (n + 1)) ^ (d - p.totalDegree) *
        homogenizeTo (R := R) p.totalDegree p := sorry

/-- In the `finSuccEquiv` presentation, reindexing successor variables gives
a constant polynomial in the first variable. -/
@[simp, stacks 061R "finSucc equivalence after tail rename"]
theorem finSuccEquiv_rename_succ {n : ℕ} (p : MvPolynomial (Fin n) R) :
    MvPolynomial.finSuccEquiv R n (MvPolynomial.rename Fin.succ p) = Polynomial.C p := sorry

/-- Dehomogenization is evaluation at `1` in the first-variable polynomial
presentation supplied by `MvPolynomial.finSuccEquiv`. -/
@[stacks 061R "dehomogenization as first-variable evaluation"]
theorem dehomogenize_eq_eval_finSuccEquiv {n : ℕ} (q : MvPolynomial (Fin (n + 1)) R) :
    dehomogenize (R := R) (n := n) q =
      Polynomial.eval (1 : MvPolynomial (Fin n) R) (MvPolynomial.finSuccEquiv R n q) := sorry

/-- A degree-`d` homogeneous polynomial dehomogenizes to the sum of its
`finSuccEquiv` coefficients through degree `d`. -/
@[stacks 061R "dehomogenization coefficient sum"]
theorem dehomogenize_eq_sum_finSuccEquiv_coeff_of_isHomogeneous {n d : ℕ}
    {q : MvPolynomial (Fin (n + 1)) R} (hq : q.IsHomogeneous d) :
    dehomogenize (R := R) (n := n) q =
      Finset.sum (Finset.range (d + 1)) fun j ↦
        (MvPolynomial.finSuccEquiv R n q).coeff j := sorry

namespace FinSuccEquiv

/-- The `i`-th first-variable coefficient of a degree-`d` homogeneous
polynomial is the `(d - i)` homogeneous component of its dehomogenization. -/
@[stacks 061R "homogeneous coefficient after dehomogenization"]
theorem coeff_eq_homogeneousComponent {n d i : ℕ}
    {q : MvPolynomial (Fin (n + 1)) R} (hq : q.IsHomogeneous d) (hi : i ≤ d) :
    (MvPolynomial.finSuccEquiv R n q).coeff i =
      MvPolynomial.homogeneousComponent (d - i) (dehomogenize (R := R) (n := n) q) := sorry

/-- The first-variable coefficients of a degree-`d` homogenization are the
homogeneous components of the source polynomial in complementary degrees. -/
@[stacks 061R "homogenization coefficient formula"]
theorem coeff_homogenizeTo {n : ℕ} (d k : ℕ)
    (p : MvPolynomial (Fin n) R) :
    (MvPolynomial.finSuccEquiv R n (homogenizeTo (R := R) d p)).coeff k =
      if k ≤ d then MvPolynomial.homogeneousComponent (d - k) p else 0 := sorry

end FinSuccEquiv

/-- Dehomogenizing a degree-`d` homogeneous polynomial cannot increase total
degree beyond `d`. -/
@[stacks 061R "dehomogenization total degree bound"]
theorem dehomogenize_totalDegree_le_of_isHomogeneous {n d : ℕ}
    {q : MvPolynomial (Fin (n + 1)) R} (hq : q.IsHomogeneous d) :
    (dehomogenize (R := R) (n := n) q).totalDegree ≤ d := sorry

/-- Homogenizing the dehomogenization of a degree-`d` homogeneous polynomial
recovers that polynomial. -/
@[stacks 061R "homogeneous reconstruction after dehomogenization"]
theorem homogenizeTo_dehomogenize_of_isHomogeneous {n d : ℕ}
    {q : MvPolynomial (Fin (n + 1)) R} (hq : q.IsHomogeneous d) :
    homogenizeTo (R := R) d (dehomogenize (R := R) (n := n) q) = q := sorry

/-- Dehomogenization is surjective, with the successor-variable rename as a
canonical representative. -/
@[stacks 061R "dehomogenization surjective"]
theorem dehomogenize_surjective {n : ℕ} :
    Function.Surjective (dehomogenize (R := R) (n := n)) := sorry

/-- Homogenization to a fixed degree commutes with finite sums. -/
@[stacks 061R "homogenization finite sum"]
theorem homogenizeTo_sum {n : ℕ} {α : Type*}
    (d : ℕ) (s : Finset α) (f : α → MvPolynomial (Fin n) R) :
    homogenizeTo (R := R) d (∑ a ∈ s, f a) =
      ∑ a ∈ s, homogenizeTo (R := R) d (f a) := sorry

/-- Homogenization commutes with the standard finite support expansion of a
multivariate polynomial. -/
@[stacks 061R "homogenization support expansion"]
theorem homogenizeTo_supportExpansion {n d : ℕ} (p : MvPolynomial (Fin n) R) :
    homogenizeTo (R := R) d p =
      ∑ m ∈ p.support,
        homogenizeTo (R := R) d (MvPolynomial.monomial m (p.coeff m)) := sorry

/-- If `p` is homogeneous of degree `i`, its degree-`d` homogenization is the
successor rename multiplied by the remaining first-variable power. -/
@[stacks 061R "homogeneous polynomial degree shift"]
theorem homogenizeTo_eq_X_zero_pow_mul_of_isHomogeneous {n i d : ℕ}
    {p : MvPolynomial (Fin n) R} (hp : p.IsHomogeneous i) (hid : i ≤ d) :
    homogenizeTo (R := R) d p =
      MvPolynomial.X (0 : Fin (n + 1)) ^ (d - i) * MvPolynomial.rename Fin.succ p := sorry

end

section

variable [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.decomposition
attribute [local instance] MvPolynomial.HomogeneousSubmodule.gradedMonoid

/-- Tag `061R`: the homogeneous ideal generated by the minimal-degree
homogenizations of elements of an affine ideal. -/
@[stacks 061R "homogenized ideal"]
noncomputable def homogenizedIdeal {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R)) :
    Ideal (MvPolynomial (Fin (n + 1)) R) :=
  Ideal.span (Set.range fun p : I ↦
    homogenizeTo (R := R) p.1.totalDegree p.1)

namespace HomogenizedIdeal

/-- Homogenize every element of an affine ideal in a degree at least `m` and take the ideal
generated by those homogeneous representatives.  The lower bound is part of the construction, so
`atLeast I 1` is the standard positive-degree variant used for affine cone charts. -/
@[stacks 061R "homogenized ideal with a degree lower bound"]
noncomputable def atLeast {n : ℕ} (I : Ideal (MvPolynomial (Fin n) R)) (m : ℕ) :
    Ideal (MvPolynomial (Fin (n + 1)) R) :=
  Ideal.span (Set.range fun p : I ↦
    homogenizeTo (R := R) (max p.1.totalDegree m) p.1)

/-- The lower-bounded homogenized ideal is homogeneous for the standard polynomial grading. -/
@[stacks 061R "lower-bounded homogenized ideal is homogeneous"]
theorem atLeast_isHomogeneous {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R)) (m : ℕ) :
    (atLeast (R := R) I m).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) := sorry

/-- Dehomogenization sends a lower-bounded homogenized ideal into its affine source ideal. -/
@[stacks 061R "lower-bounded homogenized ideal dehomogenization"]
theorem atLeast_le_comap_dehomogenize {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R)) (m : ℕ) :
    atLeast (R := R) I m ≤
      Ideal.comap (dehomogenize (R := R) (n := n)) I := sorry

/-- Every element of a positive lower-bounded homogenized ideal has zero constant coefficient.
The positivity hypothesis is explicit because `atLeast I 0` can contain constants. -/
@[stacks 061R "positive homogenized ideal constant coefficient"]
theorem constantCoeff_eq_zero_of_mem_atLeast {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R)) (hm : 0 < m)
    {q : MvPolynomial (Fin (n + 1)) R}
    (hq : q ∈ atLeast (R := R) I m) :
    MvPolynomial.constantCoeff q = 0 := sorry

/-- A constant belongs to a positive lower-bounded homogenized ideal exactly when its scalar is
zero.  This is the degree-zero separation API used by quotient charts. -/
@[stacks 061R "positive homogenized ideal constant membership"]
theorem mem_atLeast_C_iff {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R)) (hm : 0 < m) (r : R) :
    MvPolynomial.C r ∈ atLeast (R := R) I m ↔ r = 0 := sorry

/-- A homogenization of an element of the affine ideal lies in its
homogenized ideal at every sufficiently large degree. -/
@[stacks 061R "homogenized ideal contains degree shifts"]
theorem homogenizeTo_mem {n : ℕ}
    {I : Ideal (MvPolynomial (Fin n) R)} (p : I) {d : ℕ} (hp : p.1.totalDegree ≤ d) :
    homogenizeTo (R := R) d p.1 ∈ homogenizedIdeal (R := R) I := sorry

/-- A homogeneous polynomial belongs to the homogenized ideal when its
dehomogenization belongs to the affine ideal. -/
@[stacks 061R "homogenized ideal homogeneous membership"]
theorem mem_of_isHomogeneous_of_dehomogenize_mem {n d : ℕ}
    {I : Ideal (MvPolynomial (Fin n) R)} {q : MvPolynomial (Fin (n + 1)) R}
    (hq : q.IsHomogeneous d) (hdehom : dehomogenize (R := R) (n := n) q ∈ I) :
    q ∈ homogenizedIdeal (R := R) I := sorry

/-- The homogenized ideal is homogeneous for the standard polynomial
grading. -/
@[stacks 061R "homogenized ideal is homogeneous"]
theorem isHomogeneous {n : ℕ} (I : Ideal (MvPolynomial (Fin n) R)) :
    (homogenizedIdeal (R := R) I).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) := sorry

/-- Dehomogenization maps the homogenized ideal into its affine source
ideal. -/
@[stacks 061R "homogenized ideal dehomogenization compatibility"]
theorem le_comap_dehomogenize {n : ℕ} (I : Ideal (MvPolynomial (Fin n) R)) :
    homogenizedIdeal (R := R) I ≤
      Ideal.comap (dehomogenize (R := R) (n := n)) I := sorry

end HomogenizedIdeal

/-- The descended dehomogenization sends the first-variable quotient class to
`1`. -/
@[simp, stacks 061R "quotient dehomogenization on first variable"]
theorem dehomogenizeQuotient_mk_X_zero {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R))
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    (hJ : J ≤ Ideal.comap (dehomogenize (R := R) (n := n)) I) :
    Ideal.quotientMapₐ I (dehomogenize (R := R) (n := n)) hJ
        (Ideal.Quotient.mk J (MvPolynomial.X (0 : Fin (n + 1)))) = 1 := sorry

/-- The quotient class of the first variable maps to a unit under descended
dehomogenization. -/
@[stacks 061R "quotient dehomogenization first variable is a unit"]
theorem dehomogenizeQuotient_mk_X_zero_isUnit {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R))
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    (hJ : J ≤ Ideal.comap (dehomogenize (R := R) (n := n)) I) :
    IsUnit
      (Ideal.quotientMapₐ I (dehomogenize (R := R) (n := n)) hJ
        (Ideal.Quotient.mk J (MvPolynomial.X (0 : Fin (n + 1))))) := sorry

/-- The descended dehomogenization sends a successor-variable representative
to its affine quotient class. -/
@[simp, stacks 061R "quotient dehomogenization after tail rename"]
theorem dehomogenizeQuotient_mk_rename_succ {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R))
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    (hJ : J ≤ Ideal.comap (dehomogenize (R := R) (n := n)) I)
    (p : MvPolynomial (Fin n) R) :
    Ideal.quotientMapₐ I (dehomogenize (R := R) (n := n)) hJ
        (Ideal.Quotient.mk J (MvPolynomial.rename Fin.succ p)) =
      Ideal.Quotient.mk I p := sorry

/-- The descended dehomogenization sends any bounded homogenization to its
affine quotient class. -/
@[simp, stacks 061R "quotient dehomogenization after homogenization"]
theorem dehomogenizeQuotient_mk_homogenizeTo {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R))
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    (hJ : J ≤ Ideal.comap (dehomogenize (R := R) (n := n)) I)
    (d : ℕ) (p : MvPolynomial (Fin n) R) (hp : p.totalDegree ≤ d) :
    Ideal.quotientMapₐ I (dehomogenize (R := R) (n := n)) hJ
        (Ideal.Quotient.mk J (homogenizeTo (R := R) d p)) =
      Ideal.Quotient.mk I p := sorry

/-- Tag `061R`: after quotient dehomogenization, the ordinary localization
away from the first variable maps canonically to the affine quotient as an
`R`-algebra homomorphism. -/
@[stacks 061R "quotient dehomogenization away map"]
noncomputable def dehomogenizeQuotientAway {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R))
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    (hJ : J ≤ Ideal.comap (dehomogenize (R := R) (n := n)) I) :
    Localization.Away (Ideal.Quotient.mk J (MvPolynomial.X (0 : Fin (n + 1)))) →ₐ[R]
      (MvPolynomial (Fin n) R ⧸ I) :=
  IsLocalization.Away.liftAlgHom
    (S := Localization.Away (Ideal.Quotient.mk J (MvPolynomial.X (0 : Fin (n + 1)))))
    (P := MvPolynomial (Fin n) R ⧸ I) (A := R)
    (f := Ideal.quotientMapₐ I (dehomogenize (R := R) (n := n)) hJ)
    (Ideal.Quotient.mk J (MvPolynomial.X (0 : Fin (n + 1))))
    (by
      rw [Ideal.quotient_map_mkₐ]
      simp only [dehomogenize,
        MvPolynomial.Fin.evalHead, MvPolynomial.aeval_X, Fin.cases_zero,
        map_one]
      exact isUnit_one)

/-- The quotient dehomogenization map on the first-variable chart sends
`a / X₀^j` to the dehomogenized quotient class of `a`. -/
@[simp, stacks 061R "quotient dehomogenization away representative"]
theorem dehomogenizeQuotientAway_mk {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R))
    (J : Ideal (MvPolynomial (Fin (n + 1)) R))
    (hJ : J ≤ Ideal.comap (dehomogenize (R := R) (n := n)) I)
    (a : MvPolynomial (Fin (n + 1)) R ⧸ J) (j : ℕ) :
    dehomogenizeQuotientAway (R := R) (n := n) I J hJ
      (Localization.mk a
        ⟨(Ideal.Quotient.mk J (MvPolynomial.X (0 : Fin (n + 1)))) ^ j, ⟨j, rfl⟩⟩) =
      Ideal.quotientMapₐ I (dehomogenize (R := R) (n := n)) hJ a := sorry

end

end MvPolynomial.Homogenization
