/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Henselian.Noetherian
public import ReasLib.RingTheory.RingHom.IndEtale.Fiber
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fibers of henselizations

This file specializes the canonical ind-etale fiber decomposition to
henselizations and strict henselizations of Noetherian local rings.

@stack 07QQ
-/

@[expose] public section

universe u v

namespace IsHenselizationOf

variable {R : Type u} {S : Type v}
variable [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable [CommRing S] [Algebra R S] [IsHenselizationOf R S]

/-- Lemma 15.45.13 (1) (07QQ): only finitely many primes of a
henselization lie over a fixed prime of the base. -/
@[stacks 07QQ "Lemma 15.45.13 (1): primes of a henselization over a base prime"]
theorem primesOver_finite (p : PrimeSpectrum R) :
    _root_.Finite (p.asIdeal.primesOver S) := sorry

/-- Lemma 15.45.13 (2) (07QQ): the fiber of a henselization is the
product of the residue fields at the primes above the base prime. -/
@[stacks 07QQ "Lemma 15.45.13 (2): henselization fiber decomposition"]
theorem fiberToPiResidueField_bijective (p : PrimeSpectrum R) :
    Function.Bijective (p.asIdeal.fiberToPiResidueField S) := sorry

/-- Lemma 15.45.13 (5) (07QQ): residue fields of a henselization are
separable algebraic over the corresponding base residue field. -/
@[stacks 07QQ "Lemma 15.45.13 (5): henselization residue fields"]
theorem residueField_isAlgebraic_and_separable
    (p : PrimeSpectrum R) (q : p.asIdeal.primesOver S) :
    -- Local instance justification: the lies-over witness canonically fixes the residue-field
    -- algebra structure used by algebraicity and separability.
    letI : Algebra p.asIdeal.ResidueField q.1.ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver p.asIdeal q.1
    Algebra.IsAlgebraic p.asIdeal.ResidueField q.1.ResidueField ∧
      Algebra.IsSeparable p.asIdeal.ResidueField q.1.ResidueField := sorry

end IsHenselizationOf

namespace IsStrictHenselizationOf

variable {R : Type u} {S : Type v}
variable [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable [CommRing S] [Algebra R S] [IsStrictHenselizationOf R S]

/-- Lemma 15.45.13 (3) (07QQ): only finitely many primes of a strict
henselization lie over a fixed prime of the base. -/
@[stacks 07QQ "Lemma 15.45.13 (3): primes of a strict henselization over a base prime"]
theorem primesOver_finite (p : PrimeSpectrum R) :
    _root_.Finite (p.asIdeal.primesOver S) := sorry

/-- Lemma 15.45.13 (4) (07QQ): the fiber of a strict henselization is
the product of the residue fields at the primes above the base prime. -/
@[stacks 07QQ "Lemma 15.45.13 (4): strict-henselization fiber decomposition"]
theorem fiberToPiResidueField_bijective (p : PrimeSpectrum R) :
    Function.Bijective (p.asIdeal.fiberToPiResidueField S) := sorry

/-- Lemma 15.45.13 (6) (07QQ): residue fields of a strict
henselization are separable algebraic over the corresponding base residue
field. -/
@[stacks 07QQ "Lemma 15.45.13 (6): strict-henselization residue fields"]
theorem residueField_isAlgebraic_and_separable
    (p : PrimeSpectrum R) (q : p.asIdeal.primesOver S) :
    -- Local instance justification: the lies-over witness canonically fixes the residue-field
    -- algebra structure used by algebraicity and separability.
    letI : Algebra p.asIdeal.ResidueField q.1.ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver p.asIdeal q.1
    Algebra.IsAlgebraic p.asIdeal.ResidueField q.1.ResidueField ∧
      Algebra.IsSeparable p.asIdeal.ResidueField q.1.ResidueField := sorry

end IsStrictHenselizationOf
