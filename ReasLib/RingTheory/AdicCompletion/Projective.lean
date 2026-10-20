/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.FiniteType
public import ReasLib.RingTheory.AdicCompletion.MittagLeffler
public import ReasLib.RingTheory.AdicCompletion.UniversallyInjective
public import ReasLib.RingTheory.Flatness.MittagLeffler.Exact
public import ReasLib.RingTheory.Flatness.MittagLeffler.Projective

/-!
# Projectivity from adic completion

This file records a projectivity criterion for finite modules over finite-type algebras using
adic completeness and relative associated primes.
-/

@[expose] public section

universe u v w

namespace Module.Projective

/-- A finite module over a finite-type algebra is projective over a Noetherian adically complete
base when it is flat, its closed fiber is projective, and its relative associated primes avoid
the extended ideal. -/
@[stacks 05DP]
theorem of_adicComplete_of_relativeAssassin
    {R : Type u} {S : Type v} {N : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (I : Ideal R) [IsNoetherianRing R] [Algebra.FiniteType R S]
    [IsAdicComplete I R] [Module.Finite S N] [Module.Flat R N]
    [Module.Projective (R ⧸ I) (N ⧸ (I • (⊤ : Submodule R N)))]
    (h_ass : ∀ q : PrimeSpectrum S, q ∈ relativeAssassin R S N →
      I.map (algebraMap R S) + q.asIdeal ≠ ⊤) :
    Module.Projective R N := sorry

end Module.Projective
