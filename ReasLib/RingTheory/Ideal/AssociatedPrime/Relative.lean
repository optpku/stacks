/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Module

/-!
# Relative Associated Primes

This leaf owns the relative exact-annihilator associated-prime set of a module
over a ring map.  It exposes both the residue-field tensor appearing in the
definition and the equivalent fiber-module presentation.
-/

@[expose] public section

open scoped TensorProduct Algebra.TensorProduct.Right

universe u v w

section

variable (R : Type u) [CommRing R]
variable (S : Type v) [CommRing S] [Algebra R S]
variable (N : Type w) [AddCommGroup N] [Module S N] [Module R N]
variable [IsScalarTower R S N]

/-- The relative assassin of `N` over `R → S` consists of the primes `q` of `S`
exactly associated to `N ⊗[R] κ(q ∩ R)`. -/
@[stacks 05GC]
def relativeAssassin : Set (PrimeSpectrum S) :=
  { q | q.asIdeal ∈
      associatedPrimesOfModule S (N ⊗[R] (q.asIdeal.under R).ResidueField) }

end

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {N : Type w} [AddCommGroup N] [Module S N] [Module R N]
variable [IsScalarTower R S N]

/-- Membership in the relative assassin in its defining residue-field form. -/
@[simp]
theorem mem_relativeAssassin_iff (q : PrimeSpectrum S) :
    q ∈ relativeAssassin R S N ↔
      q.asIdeal ∈
        associatedPrimesOfModule S (N ⊗[R] (q.asIdeal.under R).ResidueField) := sorry

/-- Membership in the relative assassin in the equivalent fiber-module form. -/
@[stacks 05GC "relative assassin in fiber-module form"]
theorem mem_relativeAssassin_iff_fiber (q : PrimeSpectrum S) :
    q ∈ relativeAssassin R S N ↔
      q.asIdeal ∈ associatedPrimesOfModule S
        (((q.asIdeal.under R).Fiber S) ⊗[S] N) := sorry

end
