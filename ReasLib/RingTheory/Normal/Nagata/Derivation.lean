/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Finite Normalization Detected by a Derivation

@stack 0AE0

This leaf records the positive-characteristic normalization criterion for a
degree-`p` purely inseparable extension.  The derivation is stated on a chosen
fraction field and required to preserve the image of the normal domain.
-/

open Polynomial

universe u v

namespace IsIntegrallyClosed

/-- Lemma 10.161.10 (0AE0): let `R` be a Noetherian normal domain with fraction field `K` of
prime characteristic `p`.  If a derivation of `K` preserves `R` and does not kill `a`, then the
integral closure of `R` in `K[X] / (X ^ p - a)` is finite over `R`. -/
@[stacks 0AE0]
theorem integralClosure_adjoinRoot_pthSub_finite_of_derivation
    {R : Type u} {K : Type v}
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {p : ℕ} [Fact p.Prime] [CharP K p] (a : K)
    (hD : ∃ D : Derivation ℤ K K,
      Set.MapsTo D (Set.range (algebraMap R K)) (Set.range (algebraMap R K)) ∧ D a ≠ 0) :
    Module.Finite R (integralClosure R (AdjoinRoot (X ^ p - C a))) := sorry

end IsIntegrallyClosed
