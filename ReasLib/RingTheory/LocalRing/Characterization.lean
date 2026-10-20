/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Characterizations of local rings

@stack 00E9

This leaf packages the standard algebraic and topological characterizations
of a commutative local ring.
-/

@[expose] public section

universe u

namespace IsLocalRing

/-- Lemma 10.18.3 (Stacks `00E9`): a ring is local exactly when its spectrum
has one closed point, when the complement of one maximal ideal is the set of
units, or when every element or its complement is a unit. -/
@[stacks 00E9]
theorem tfae (R : Type u) [CommRing R] :
    List.TFAE
      [ IsLocalRing R
      , ∃! x : PrimeSpectrum R, IsClosed ({x} : Set (PrimeSpectrum R))
      , ∃ m : MaximalSpectrum R, ∀ x : R, x ∉ m.asIdeal ↔ IsUnit x
      , Nontrivial R ∧ ∀ x : R, IsUnit x ∨ IsUnit (1 - x)
      ] := sorry

end IsLocalRing
