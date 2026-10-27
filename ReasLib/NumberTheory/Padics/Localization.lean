/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.NumberTheory.Padics.RingHoms
public import ReasLib.RingTheory.Localization.AtPrime.Int

@[expose] public section

noncomputable section

namespace PadicInt

/-- The canonical map `ℤ_(p) → ℤ_[p]`, sending a fraction with denominator outside `(p)`
to its image under `ℤ → ℤ_[p]`. -/
def fromLocalization (p : ℕ) [Fact p.Prime] : Int.LocalizationAtPrime p →+* ℤ_[p] :=
  let g : ℤ →+* ℤ_[p] := Int.castRingHom ℤ_[p]
  let hg : ∀ y : (Ideal.span ({(p : ℤ)} : Set ℤ)).primeCompl, IsUnit (g y) :=
    fun y ↦
      PadicInt.isUnit_iff.mpr <|
        le_antisymm (PadicInt.norm_le_one (g y)) <|
          le_of_not_gt <|
            (PadicInt.norm_intCast_lt_one_iff :
                ‖(y.1 : ℤ_[p])‖ < 1 ↔ (p : ℤ) ∣ y.1).not.mpr <|
              (Ideal.mem_span_singleton :
                  y.1 ∈ Ideal.span {(p : ℤ)} ↔ (p : ℤ) ∣ y.1).not.mp y.2
  IsLocalization.lift hg

/-- `fromLocalization` extends the canonical map from `ℤ`. -/
theorem fromLocalization_algebraMap (p : ℕ) [Fact p.Prime] (n : ℤ) :
    fromLocalization p (algebraMap ℤ (Int.LocalizationAtPrime p) n) = n := sorry

/-- The canonical `ℤ_(p)`-algebra structure on `ℤ_[p]`. -/
instance instAlgebraLocalizationAtPrime (p : ℕ) [Fact p.Prime] :
    Algebra (Int.LocalizationAtPrime p) ℤ_[p] :=
  (fromLocalization p).toAlgebra

/-- Reduction `ℤ_[p] → ZMod p` is the structure map of an algebra. -/
instance instAlgebraZMod (p : ℕ) [Fact p.Prime] : Algebra ℤ_[p] (ZMod p) :=
  PadicInt.toZMod.toAlgebra

/-- The algebra map `ℤ_[p] → ZMod p` is `PadicInt.toZMod`. -/
theorem algebraMap_toZMod (p : ℕ) [Fact p.Prime] :
    algebraMap ℤ_[p] (ZMod p) = PadicInt.toZMod := rfl

end PadicInt
