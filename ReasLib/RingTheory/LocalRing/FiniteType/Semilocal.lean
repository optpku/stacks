/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.KrullDimension.LocalRing
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Semilocal finite-type algebras over one-dimensional local domains

This leaf owns the semilocality consequence of a finite-type domain map whose
extension of fraction fields is finite. The result is stated at
`MaximalSpectrum`, since finiteness of the closed-point index is the reusable
conclusion; source-specific order-of-vanishing arguments should consume this
fact rather than rebuild the generic-fiber/closed-fiber case split.

@stack 02MM
-/

namespace MaximalSpectrum

universe u v

/-- Stacks Lemma 10.124.1 (1), tag `02MM`: a finite-type domain over a Noetherian local domain of
Krull dimension at most one has finite maximal spectrum when its fraction field is
finite-dimensional over that of the base. -/
@[stacks 02MM "(1)"]
theorem finite_of_finiteType_fractionRing
    (R : Type u) {S : Type v} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [Algebra R S] [IsLocalRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    [Algebra.FiniteType R S] [Algebra (FractionRing R) (FractionRing S)]
    [IsScalarTower R (FractionRing R) (FractionRing S)]
    [FiniteDimensional (FractionRing R) (FractionRing S)] :
    Finite (MaximalSpectrum S) := sorry

end MaximalSpectrum
