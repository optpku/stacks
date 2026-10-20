/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.Defs
public import Mathlib.SetTheory.Cardinal.Basic

@[expose] public section

noncomputable section

universe u

open scoped Cardinal

namespace PrimeSpectrum

/-- The product of residue fields of a commutative ring `R`, indexed by `PrimeSpectrum R`. -/
abbrev residueFieldPi (R : Type u) [CommRing R] : Type u :=
  (p : PrimeSpectrum R) → p.asIdeal.ResidueField

/-- The cardinality of the product of residue fields of a commutative ring `R` is at most
`#R ^ ((2 : Cardinal.{u}) ^ #R)`. -/
theorem cardinalMk_residueFieldPi_le {R : Type u} [CommRing R] :
    #(residueFieldPi R) ≤ #R ^ ((2 : Cardinal.{u}) ^ #R) := sorry

/-- The cardinality of the product of residue fields of `Polynomial ℂ` is not bounded by
`#(Polynomial ℂ) ^ ℵ₀`. -/
theorem cardinalMk_residueFieldPi_complexPolynomial_not_le_power_aleph0 :
    ¬ #(residueFieldPi (Polynomial ℂ)) ≤ #(Polynomial ℂ) ^ ℵ₀ := sorry

/-- The cardinality of the product of residue fields of `ℕ → ZMod 2` is not bounded by
`#(ℕ → ZMod 2) ^ #(ℕ → ZMod 2)`. -/
theorem cardinalMk_residueFieldPi_piZModTwo_not_le_power_self :
    ¬ #(residueFieldPi (ℕ → ZMod 2)) ≤ #(ℕ → ZMod 2) ^ #(ℕ → ZMod 2) := sorry

end PrimeSpectrum
