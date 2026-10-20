/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.DividedPowers.DPMorphism
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ReasLib.RingTheory.DividedPowers.Padic
public import ReasLib.RingTheory.Localization.AtPrime.Int
public import stacks_project.Chap60.«60_17_0_1»

@[expose] public section

noncomputable section

open DividedPowers

namespace Crystalline.AffineSpace

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
    algebraMap ℤ_[p] (ZMod p) = PadicInt.toZMod := sorry

/-- The polynomial ring `P = ℤ_[p][x₁,…,x_r]`. -/
abbrev polynomialRing (p r : ℕ) [Fact p.Prime] : Type :=
  MvPolynomial (Fin r) ℤ_[p]

/-- `polynomialRing` is the multivariate polynomial ring on `Fin r`. -/
theorem polynomialRing_eq (p r : ℕ) [Fact p.Prime] :
    polynomialRing p r = MvPolynomial (Fin r) ℤ_[p] := sorry

/-- The coordinate ring `C = (ZMod p)[x₁,…,x_r]` of affine space over `𝔽_p`. -/
abbrev coordinateRing (p r : ℕ) [Fact p.Prime] : Type :=
  MvPolynomial (Fin r) (ZMod p)

/-- `coordinateRing` is the multivariate polynomial ring over `ZMod p`. -/
theorem coordinateRing_eq (p r : ℕ) [Fact p.Prime] :
    coordinateRing p r = MvPolynomial (Fin r) (ZMod p) := sorry

/-- The presentation map `P → C`, reducing polynomial coefficients modulo `p`. -/
def modP (p r : ℕ) [Fact p.Prime] : polynomialRing p r →ₐ[ℤ_[p]] coordinateRing p r :=
  MvPolynomial.mapAlgHom (Algebra.ofId ℤ_[p] (ZMod p))

/-- Coefficient reduction `P → C` is surjective. -/
theorem modP_surjective (p r : ℕ) [Fact p.Prime] : Function.Surjective (modP p r) := sorry

/-- The kernel of coefficient reduction is the principal ideal `(p)`. -/
theorem ker_modP_eq_span_p (p r : ℕ) [Fact p.Prime] :
    RingHom.ker (modP p r).toRingHom = Ideal.span {(p : polynomialRing p r)} := sorry

/-- The image of `(p) ⊂ ℤ_[p]` in `C` is zero. -/
theorem modP_prime_bot (p r : ℕ) [Fact p.Prime] :
    Ideal.map (algebraMap ℤ_[p] (coordinateRing p r)) (Ideal.span {(p : ℤ_[p])}) =
      (⊥ : Ideal (coordinateRing p r)) := sorry

/-- The integer `p` is nilpotent on `C`. -/
theorem coordinate_p_nilpotent (p r : ℕ) [Fact p.Prime] :
    IsNilpotent (p : coordinateRing p r) := sorry

/-- The principal ideal `(p) ⊂ ℤ_[p]`. -/
abbrev padicIdeal (p : ℕ) [Fact p.Prime] : Ideal ℤ_[p] :=
  Ideal.span {(p : ℤ_[p])}

/-- `padicIdeal` is the span of the prime element. -/
theorem padicIdeal_eq (p : ℕ) [Fact p.Prime] :
    padicIdeal p = Ideal.span {(p : ℤ_[p])} := sorry

/-- The image of `(p)` in `P` is contained in the principal ideal `(p) ⊂ P`. -/
theorem primeMap_le (p r : ℕ) [Fact p.Prime] :
    Ideal.map (algebraMap ℤ_[p] (polynomialRing p r)) (padicIdeal p) ≤
      Ideal.span {(p : polynomialRing p r)} := sorry

/-- The unique divided-power structure on `(p) ⊂ P` extending
`PadicInt.dividedPowers p` along `ℤ_[p] → P`. -/
def dividedPowersPrime (p r : ℕ) [Fact p.Prime] :
    DividedPowers (Ideal.span {(p : polynomialRing p r)}) :=
  Classical.choose PadicInt.existsUnique_dividedPowers_span_prime

/-- Divided powers on `(p) ⊂ P` are the canonical coefficient formula. -/
theorem dividedPowersPrime_dpow (p r n : ℕ) [Fact p.Prime] (a : polynomialRing p r) :
    (dividedPowersPrime p r).dpow n ((p : polynomialRing p r) * a) =
      algebraMap ℤ_[p] (polynomialRing p r)
          ((PadicInt.dividedPowers p).dpow n (p : ℤ_[p])) * a ^ n := sorry

/-- The coefficient formula determines the divided powers on `(p) ⊂ P`. -/
theorem dividedPowersPrime_unique (p r : ℕ) [Fact p.Prime]
    (γ : DividedPowers (Ideal.span {(p : polynomialRing p r)}))
    (hγ : ∀ n a, γ.dpow n ((p : polynomialRing p r) * a) =
      algebraMap ℤ_[p] (polynomialRing p r)
          ((PadicInt.dividedPowers p).dpow n (p : ℤ_[p])) * a ^ n) :
    γ = dividedPowersPrime p r := sorry

/-- Extension of the canonical divided powers on `(p) ⊂ ℤ_[p]` along `ℤ_[p] → P`. -/
def dividedPowersPrimeMorphism (p r : ℕ) [Fact p.Prime] :
    DividedPowers.DPMorphism (PadicInt.dividedPowers p) (dividedPowersPrime p r) where
  toRingHom := algebraMap ℤ_[p] (polynomialRing p r)
  ideal_comp := sorry
  dpow_comp := sorry

/-- The divided-power morphism is the polynomial structure map on underlying rings. -/
theorem dividedPowersPrimeMorphism_toRingHom (p r : ℕ) [Fact p.Prime] :
    (dividedPowersPrimeMorphism p r).toRingHom =
      algebraMap ℤ_[p] (polynomialRing p r) := sorry

/-- The identity-like divided-power envelope of `P` along `(p)`, in the sense of §60.17. -/
def envelope (p r : ℕ) [Fact p.Prime] :
    DividedPowerEnvelope (padicIdeal p) (PadicInt.dividedPowers p)
      (algebraMap ℤ_[p] (polynomialRing p r))
      (Ideal.span {(p : polynomialRing p r)}) (primeMap_le p r) where
  D := DividedPowerRing.of (polynomialRing p r)
    (Ideal.span {(p : polynomialRing p r)}) (dividedPowersPrime p r)
  base := dividedPowersPrimeMorphism p r
  toD := RingHom.id (polynomialRing p r)
  toQuotient := Ideal.Quotient.mk (Ideal.span {(p : polynomialRing p r)})
  base_toD := sorry
  ideal_map := sorry
  quotient_comp := sorry

/-- The envelope is the identity on `P` followed by the quotient by `(p)`. -/
theorem envelope_spec (p r : ℕ) [Fact p.Prime] :
    (envelope p r).toD = RingHom.id (polynomialRing p r) ∧
      (envelope p r).toQuotient.comp (envelope p r).toD =
        Ideal.Quotient.mk (Ideal.span {(p : polynomialRing p r)}) := sorry

/-- The identity envelope of `P` along `(p)` is a divided-power envelope. -/
theorem envelope_isUniversal (p r : ℕ) [Fact p.Prime] :
    DividedPowerEnvelope.IsUniversal (PadicInt.dividedPowers p)
      (algebraMap ℤ_[p] (polynomialRing p r)) (primeMap_le p r) (envelope p r) := sorry

/-- The p-adic completion `D` of `P` as a `ℤ_[p]`-module. -/
abbrev completedRing (p r : ℕ) [Fact p.Prime] : Type :=
  AdicCompletion (padicIdeal p) (polynomialRing p r)

/-- `completedRing` is the `(p)`-adic completion of `P`. -/
theorem completedRing_eq (p r : ℕ) [Fact p.Prime] :
    completedRing p r = AdicCompletion (padicIdeal p) (polynomialRing p r) := sorry

/-- Crystalline `D` from the identity envelope is the ring-adic completion of `P` at `(p)`. -/
theorem envelope_crystallineD_eq (p r : ℕ) [Fact p.Prime] :
    crystallineD p (padicIdeal p) (PadicInt.dividedPowers p) (modP p r) (modP_surjective p r)
        (Ideal.span {(p : polynomialRing p r)}) (ker_modP_eq_span_p p r).symm
        (modP_prime_bot p r) (coordinate_p_nilpotent p r) (primeMap_le p r)
        (envelope p r) (envelope_isUniversal p r) =
      AdicCompletion (Ideal.span {(p : polynomialRing p r)}) (polynomialRing p r) := sorry

end Crystalline.AffineSpace
