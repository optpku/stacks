/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Spectrum.Prime.ResidueFieldProduct
import StacksCheckRecall

universe u

open scoped Cardinal

/- Remark 3.9.10 (1). The product of all prime residue fields of a commutative ring `R`
has cardinality at most `#R ^ ((2 : Cardinal.{u}) ^ #R)`. This larger bound may replace
the bound used in constructing categories of schemes when such products are needed. -/
@[stacks 000S] #check (PrimeSpectrum.cardinalMk_residueFieldPi_le :
  ∀ {R : Type u} [CommRing R],
    #(PrimeSpectrum.residueFieldPi R) ≤ #R ^ ((2 : Cardinal.{u}) ^ #R))

/- Remark 3.9.10 (2). For `R = Polynomial ℂ`, the product of all prime residue fields
is not bounded in cardinality by `#R ^ ℵ₀`. -/
@[stacks 000S] #check
  (PrimeSpectrum.cardinalMk_residueFieldPi_complexPolynomial_not_le_power_aleph0 :
    ¬ #(PrimeSpectrum.residueFieldPi (Polynomial ℂ)) ≤ #(Polynomial ℂ) ^ ℵ₀)

/- Remark 3.9.10 (3). For `R = ℕ → ZMod 2`, the product of all prime residue fields
is not bounded in cardinality by `#R ^ #R`. -/
@[stacks 000S] #check
  (PrimeSpectrum.cardinalMk_residueFieldPi_piZModTwo_not_le_power_self :
    ¬ #(PrimeSpectrum.residueFieldPi (ℕ → ZMod 2)) ≤ #(ℕ → ZMod 2) ^ #(ℕ → ZMod 2))
