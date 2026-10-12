/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe u

noncomputable section

namespace ZeroDimFlatIdeal

open MvPolynomial

variable (k : Type u)

/-- The two families of variables `X i` and `Y i` in the presentation. -/
inductive Var
  | x : ℕ → Var
  | y : ℕ → Var
  deriving DecidableEq

section

variable [CommRing k]

/-- The ambient polynomial ring `k[X i, Y i]`. -/
abbrev PolynomialRing : Type u := MvPolynomial Var k

/-- The relation `X i - Y i * X (i + 1)`. -/
def xRecurrence (i : ℕ) : PolynomialRing k :=
  X (.x i) - X (.y i) * X (.x (i + 1))

/-- The relation `Y i ^ 2`. -/
def ySquare (i : ℕ) : PolynomialRing k :=
  X (.y i) ^ 2

/-- The two infinite families of defining relations. -/
def relations : Set (PolynomialRing k) :=
  Set.range (xRecurrence k) ∪ Set.range (ySquare k)

/-- The defining ideal `(X i - Y i * X (i + 1), Y i ^ 2)`. -/
def relationIdeal : Ideal (PolynomialRing k) :=
  Ideal.span (relations k)

/-- The quotient ring `k[X i, Y i] ⧸ (X i - Y i * X (i + 1), Y i ^ 2)`. -/
abbrev Ring : Type u := PolynomialRing k ⧸ relationIdeal k

/-- The image of `X i` in the quotient. -/
def x (i : ℕ) : Ring k :=
  Ideal.Quotient.mk (relationIdeal k) (X (.x i))

/-- The image of `Y i` in the quotient. -/
def y (i : ℕ) : Ring k :=
  Ideal.Quotient.mk (relationIdeal k) (X (.y i))

/-- The ideal `m = (x i, y i)`. -/
def maximalIdeal : Ideal (Ring k) :=
  Ideal.span (Set.range (x k) ∪ Set.range (y k))

/-- The ideal `I = (x i)`. -/
def xIdeal : Ideal (Ring k) :=
  Ideal.span (Set.range (x k))

/-- Each recurrence polynomial lies in the defining ideal. -/
theorem xRecurrence_mem_relationIdeal (i : ℕ) :
    xRecurrence k i ∈ relationIdeal k := sorry

/-- Each square polynomial lies in the defining ideal. -/
theorem ySquare_mem_relationIdeal (i : ℕ) :
    ySquare k i ∈ relationIdeal k := sorry

/-- The images satisfy `x i = y i * x (i + 1)`. -/
theorem x_eq_y_mul_x_succ (i : ℕ) : x k i = y k i * x k (i + 1) := sorry

/-- The images satisfy `y i ^ 2 = 0`. -/
theorem y_sq (i : ℕ) : y k i ^ 2 = 0 := sorry

/-- Each generator `x i` lies in `I = (x i)`. -/
theorem x_mem_xIdeal (i : ℕ) : x k i ∈ xIdeal k := sorry

/-- Each generator `x i` lies in `m = (x i, y i)`. -/
theorem x_mem_maximalIdeal (i : ℕ) : x k i ∈ maximalIdeal k := sorry

/-- Each generator `y i` lies in `m = (x i, y i)`. -/
theorem y_mem_maximalIdeal (i : ℕ) : y k i ∈ maximalIdeal k := sorry

end

section

variable [Field k]

/-- The presented quotient is a local ring. -/
instance instIsLocalRing : IsLocalRing (Ring k) := sorry

/-- The presented quotient has Krull dimension at most `0`. -/
instance instKrullDimLE : _root_.Ring.KrullDimLE 0 (Ring k) := sorry

/-- The ideal `(x i)` is flat as a module over the presented quotient. -/
instance instFlat_xIdeal : Module.Flat (Ring k) (xIdeal k) := sorry

/-- The ideal `I = (x i)` is nonzero. -/
theorem xIdeal_ne_bot : xIdeal k ≠ ⊥ := sorry

/-- The ideal `I = (x i)` is proper. -/
theorem xIdeal_ne_top : xIdeal k ≠ ⊤ := sorry

/-- The presented quotient has a unique prime ideal. -/
theorem existsUnique_isPrime : ∃! p : Ideal (Ring k), p.IsPrime := sorry

/-- A prime ideal of the presented quotient is exactly `m = (x i, y i)`. -/
theorem isPrime_iff_eq_maximalIdeal {p : Ideal (Ring k)} :
    p.IsPrime ↔ p = maximalIdeal k := sorry

end

end ZeroDimFlatIdeal

/-- Lemma 110.35.1: there exists a local ring `R` with a unique prime ideal and a
nonzero ideal `I ⊆ R` which is a flat `R`-module. -/
@[stacks 05G0]
theorem exists_isLocalRing_uniquePrime_nonzero_flat_ideal :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsLocalRing R) (I : Ideal R),
      (∃! p : Ideal R, p.IsPrime) ∧ I ≠ ⊥ ∧ I ≠ ⊤ ∧ Module.Flat R I := sorry
