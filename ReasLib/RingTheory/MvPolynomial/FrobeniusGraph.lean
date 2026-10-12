/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.Group.Irreducible.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.ZMod.Basic

@[expose] public section

noncomputable section

namespace MvPolynomial.FrobeniusGraph

/-- The four source coordinates used by the Frobenius-graph specialization. -/
inductive Coord where
  /-- The first source coordinate. -/
  | x
  /-- The second source coordinate. -/
  | y
  /-- The third source coordinate. -/
  | u
  /-- The fourth source coordinate. -/
  | v
  deriving DecidableEq

/-- The ring homomorphism reducing integer coefficients modulo `p` and sending
the four coordinates to `x`, `y`, `x ^ p`, and `y ^ p`, respectively. -/
def specialize (p : ℕ) : MvPolynomial Coord ℤ →+* MvPolynomial (Fin 2) (ZMod p) :=
  eval₂Hom (C.comp (Int.castRingHom (ZMod p))) fun
    | .x => X (0 : Fin 2)
    | .y => X (1 : Fin 2)
    | .u => X (0 : Fin 2) ^ p
    | .v => X (1 : Fin 2) ^ p

/-- The Frobenius-graph specialization sends a constant polynomial to its
coefficient reduced modulo `p`. -/
theorem specialize_C (p : ℕ) (a : ℤ) :
    specialize p (C a) = C (Int.castRingHom (ZMod p) a) := sorry

/-- The Frobenius-graph specialization sends the first source coordinate to
the first target coordinate. -/
theorem specialize_X_x (p : ℕ) : specialize p (X .x) = X (0 : Fin 2) := sorry

/-- The Frobenius-graph specialization sends the second source coordinate to
the second target coordinate. -/
theorem specialize_X_y (p : ℕ) : specialize p (X .y) = X (1 : Fin 2) := sorry

/-- The Frobenius-graph specialization sends the third source coordinate to
the `p`-th power of the first target coordinate. -/
theorem specialize_X_u (p : ℕ) : specialize p (X .u) = X (0 : Fin 2) ^ p := sorry

/-- The Frobenius-graph specialization sends the fourth source coordinate to
the `p`-th power of the second target coordinate. -/
theorem specialize_X_v (p : ℕ) : specialize p (X .v) = X (1 : Fin 2) ^ p := sorry

/-- Evaluation of a specialized polynomial is evaluation on the Frobenius
graph after reducing its integer coefficients modulo `p`. -/
theorem specialize_apply (p : ℕ) (f : MvPolynomial Coord ℤ) (xy : Fin 2 → ZMod p) :
    eval xy (specialize p f) =
      eval₂ (Int.castRingHom (ZMod p)) (fun
        | .x => xy 0
        | .y => xy 1
        | .u => xy 0 ^ p
        | .v => xy 1 ^ p) f := sorry

/-- An irreducible integer polynomial in four coordinates has Frobenius-graph
specializations factoring into two positive-total-degree plane polynomials at
all sufficiently large primes. -/
def eventualPlaneFactorization (f : MvPolynomial Coord ℤ) : Prop :=
  Irreducible f ∧ ∃ N : ℕ, ∀ p : ℕ, p.Prime → N ≤ p →
    ∃ g1 g2 : MvPolynomial (Fin 2) (ZMod p),
      specialize p f = g1 * g2 ∧ 0 < g1.totalDegree ∧ 0 < g2.totalDegree

/-- Eventual plane factorization is equivalent to irreducibility over the
integers and factorization into two positive-total-degree factors after
Frobenius-graph specialization at all sufficiently large primes. -/
theorem eventualPlaneFactorization_iff (f : MvPolynomial Coord ℤ) :
    eventualPlaneFactorization f ↔
      Irreducible f ∧ ∃ N : ℕ, ∀ p : ℕ, p.Prime → N ≤ p →
        ∃ g1 g2 : MvPolynomial (Fin 2) (ZMod p),
          specialize p f = g1 * g2 ∧ 0 < g1.totalDegree ∧ 0 < g2.totalDegree := sorry

end MvPolynomial.FrobeniusGraph
