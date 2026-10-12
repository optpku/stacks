/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Jacobian matrices of multivariable polynomials

This file defines Jacobian matrices evaluated in residue fields and at the origin,
and states regularity and dimension criteria for polynomial quotients at the origin.
-/

@[expose] public section

noncomputable section

universe u v w

namespace MvPolynomial

variable {R : Type u} [CommRing R] {σ : Type v} {ι : Type w}

/-- The Jacobian matrix of a family of multivariable polynomials, evaluated in the
residue field at a prime ideal. -/
noncomputable def jacobiMatrixAt (g : ι → MvPolynomial σ R)
    (q : Ideal (MvPolynomial σ R)) [q.IsPrime] : Matrix σ ι q.ResidueField :=
  fun j i ↦ algebraMap (MvPolynomial σ R) q.ResidueField (pderiv j (g i))

/-- An entry of `jacobiMatrixAt g q` is the corresponding partial derivative mapped to the
residue field at `q`. -/
theorem jacobiMatrixAt_apply (g : ι → MvPolynomial σ R)
    (q : Ideal (MvPolynomial σ R)) [q.IsPrime] (j : σ) (i : ι) :
    jacobiMatrixAt g q j i =
      algebraMap (MvPolynomial σ R) q.ResidueField (pderiv j (g i)) := sorry

/-- For a square Jacobian over a residue field, full rank is equivalent to bijectivity of the
associated linear map on coordinate vectors. -/
theorem jacobiMatrixAt_rank_eq_iff_bijective {n : ℕ}
    (g : Fin n → MvPolynomial (Fin n) R)
    (q : Ideal (MvPolynomial (Fin n) R)) [q.IsPrime] :
    (jacobiMatrixAt g q).rank = n ↔
      Function.Bijective (jacobiMatrixAt g q).mulVecLin := sorry

/-- The Jacobian matrix of a finite polynomial family, with relation rows and variable
columns, evaluated at the origin. -/
def jacobianAtOrigin {k : Type u} [Field k] {n c : ℕ}
    (f : Fin c → MvPolynomial (Fin n) k) : Matrix (Fin c) (Fin n) k :=
  fun j i ↦ eval (0 : Fin n → k) (pderiv i (f j))

/-- A Jacobian entry at the origin is the corresponding evaluated partial derivative. -/
theorem jacobianAtOrigin_apply {k : Type u} [Field k] {n c : ℕ}
    (f : Fin c → MvPolynomial (Fin n) k) (j : Fin c) (i : Fin n) :
    jacobianAtOrigin f j i = eval (0 : Fin n → k) (pderiv i (f j)) := sorry

/-- The coordinate ring of a finite polynomial presentation is the quotient by its relations. -/
abbrev coordRing (k : Type u) [Field k] (n : ℕ) {c : ℕ}
    (f : Fin c → MvPolynomial (Fin n) k) : Type u :=
  MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range f)

/-- The origin ideal in a polynomial quotient is the image of the ideal of variables. -/
def originIdeal (k : Type u) [Field k] (n : ℕ) {c : ℕ}
    (f : Fin c → MvPolynomial (Fin n) k) : Ideal (coordRing k n f) :=
  Ideal.map (Ideal.Quotient.mk (Ideal.span (Set.range f))) (idealOfVars (Fin n) k)

/-- The origin ideal is the extension of the ideal of variables along the quotient map. -/
theorem originIdeal_eq_map (k : Type u) [Field k] (n : ℕ) {c : ℕ}
    (f : Fin c → MvPolynomial (Fin n) k) :
    originIdeal k n f =
      Ideal.map (Ideal.Quotient.mk (Ideal.span (Set.range f))) (idealOfVars (Fin n) k) := sorry

/-- If every relation vanishes at the origin, the origin ideal in the quotient is maximal. -/
theorem originIdeal_isMaximal {k : Type u} [Field k] {n c : ℕ}
    (f : Fin c → MvPolynomial (Fin n) k)
    (h0 : ∀ j, eval (0 : Fin n → k) (f j) = 0) :
    (originIdeal k n f).IsMaximal := sorry

/-- A polynomial quotient localized at the origin is regular when its relations vanish
there and the Jacobian has full row rank. -/
theorem isRegularLocalRing_of_jacobianRank {k : Type u} [Field k] {n c : ℕ}
    (f : Fin c → MvPolynomial (Fin n) k)
    (h0 : ∀ j, eval (0 : Fin n → k) (f j) = 0)
    (hrank : (jacobianAtOrigin f).rank = c) :
    IsRegularLocalRing (Localization.AtPrime (originIdeal k n f)
      (hp := (originIdeal_isMaximal f h0).isPrime)) := sorry

/-- A polynomial quotient with vanishing relations and full Jacobian row rank has local
Krull dimension equal to the number of variables minus the number of relations. -/
theorem ringKrullDim_eq_of_jacobianRank {k : Type u} [Field k] {n c : ℕ}
    (f : Fin c → MvPolynomial (Fin n) k)
    (h0 : ∀ j, eval (0 : Fin n → k) (f j) = 0)
    (hrank : (jacobianAtOrigin f).rank = c) :
    ringKrullDim (Localization.AtPrime (originIdeal k n f)
      (hp := (originIdeal_isMaximal f h0).isPrime)) = n - c := sorry

/-- The repeated coordinate relation `X 0, X 0` in two variables. -/
def redundantRelations (k : Type u) [Field k] : Fin 2 → MvPolynomial (Fin 2) k :=
  fun _ ↦ X (0 : Fin 2)

/-- Each repeated relation is the first coordinate polynomial. -/
theorem redundantRelations_apply (k : Type u) [Field k] (j : Fin 2) :
    redundantRelations k j = X (0 : Fin 2) := sorry

/-- Each repeated coordinate relation vanishes at the origin. -/
theorem redundantRelations_eval_zero (k : Type u) [Field k] (j : Fin 2) :
    eval (0 : Fin 2 → k) (redundantRelations k j) = 0 := sorry

/-- The origin ideal in the quotient by the repeated coordinate relation is maximal. -/
theorem redundantOriginIdeal_isMaximal (k : Type u) [Field k] :
    (originIdeal k 2 (redundantRelations k)).IsMaximal := sorry

/-- The quotient by the repeated coordinate relation is regular after localization
at the origin. -/
theorem redundant_isRegularLocalRing (k : Type u) [Field k] :
    IsRegularLocalRing (Localization.AtPrime (originIdeal k 2 (redundantRelations k))
      (hp := (redundantOriginIdeal_isMaximal k).isPrime)) := sorry

/-- The Jacobian of the repeated coordinate relation at the origin has rank less than two. -/
theorem redundant_jacobianRank_lt (k : Type u) [Field k] :
    (jacobianAtOrigin (redundantRelations k)).rank < 2 := sorry

/-- The quotient by the repeated coordinate relation has local Krull dimension one
at the origin. -/
theorem redundant_ringKrullDim (k : Type u) [Field k] :
    ringKrullDim (Localization.AtPrime (originIdeal k 2 (redundantRelations k))
      (hp := (redundantOriginIdeal_isMaximal k).isPrime)) = 1 := sorry

end MvPolynomial
