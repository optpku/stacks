/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.RingTheory.Length
public import ReasLib.Algebra.Category.ModuleCat.Tor.Independence
public import ReasLib.Algebra.Category.ModuleCat.Tor.Vanishing

/-!
# Euler characteristic of module Tor

This module records the integer-valued alternating sum of the lengths of the
Tor modules of two bundled modules.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.Tor

variable {R : Type u} [CommRing R]

/-- The Euler characteristic of two bundled modules is the signed finsum of
the natural-valued lengths of their Tor modules. -/
noncomputable def eulerCharacteristic (M N : ModuleCat.{u} R) : ℤ :=
  ∑ᶠ p : ℕ, (Int.negOnePow p : ℤ) * ((Module.length R (obj p M N)).toNat : ℤ)

/-- The Euler characteristic is given by the signed finsum of Tor lengths. -/
theorem eulerCharacteristic_apply (M N : ModuleCat.{u} R) :
    eulerCharacteristic M N =
      ∑ᶠ p : ℕ, (Int.negOnePow p : ℤ) * ((Module.length R (obj p M N)).toNat : ℤ) := sorry

/-- A bound above which Tor vanishes reduces the Euler characteristic to a finite sum. -/
theorem eulerCharacteristic_eq_sum_range (M N : ModuleCat.{u} R) (d : ℕ)
    (h : IsZeroAbove M N d) :
    eulerCharacteristic M N =
      ∑ p ∈ Finset.range (d + 1),
        (Int.negOnePow p : ℤ) * ((Module.length R (obj p M N)).toNat : ℤ) := sorry

/-- The Euler characteristic is invariant under isomorphisms of both modules. -/
theorem eulerCharacteristic_congr {M M' N N' : ModuleCat.{u} R}
    (eM : M ≅ M') (eN : N ≅ N') :
    eulerCharacteristic M N = eulerCharacteristic M' N' := sorry

end CategoryTheory.ModuleCat.Tor
