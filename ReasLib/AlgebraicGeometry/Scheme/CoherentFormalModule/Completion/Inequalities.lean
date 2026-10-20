/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Order.WithBotTop
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.Local
public import ReasLib.RingTheory.Depth

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- A coherent formal module satisfies the ordinary `(a, b)` depth and dimension inequalities at every completed local prime. -/
def SatisfiesInequalities (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)) (a b : ℤ) : Prop :=
  ∀ y : S.Y, (hy : S.y y ∈ S.U) →
    let yU := closedFiberOpenPoint S y hy
    ∀ p : PrimeSpectrum (completedLocalRing S yU),
        p ∉ PrimeSpectrum.zeroLocus (completedIdeal S yU : Set (completedLocalRing S yU)) →
          let depth : EInt := enatToEInt <|
            moduleDepth (Localization.AtPrime p.asIdeal)
              (LocalizedModule.AtPrime p.asIdeal (completedStalk S F yU))
          let δ : EInt := enatToEInt (algebraizationDistance S y)
          if PrimeSpectrum.zeroLocus p.asIdeal ∩
                PrimeSpectrum.zeroLocus
                  (completedIdeal S yU : Set (completedLocalRing S yU)) =
              {q | q.asIdeal = completedMaximalIdeal S yU}
          then (a : EInt) < depth + δ
          else (a : EInt) ≤ depth + δ ∨
            (b : EInt) < depth +
              WithBot.map (WithTop.map Int.ofNat)
                (ringKrullDim (completedLocalRing S yU ⧸ p.asIdeal)) + δ

/-- Applying the ordinary inequalities at a point gives the corresponding depth or dimension alternative. -/
theorem satisfiesInequalities_apply (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)) (a b : ℤ)
    (hF : SatisfiesInequalities S F a b) (y : S.Y) (hy : S.y y ∈ S.U)
    (p : PrimeSpectrum (completedLocalRing S (closedFiberOpenPoint S y hy)))
    (hp : p ∉ PrimeSpectrum.zeroLocus
      (completedIdeal S (closedFiberOpenPoint S y hy) :
        Set (completedLocalRing S (closedFiberOpenPoint S y hy)))) :
    let yU := closedFiberOpenPoint S y hy
    let depth : EInt := enatToEInt <|
      moduleDepth (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal (completedStalk S F yU))
    let δ : EInt := enatToEInt (algebraizationDistance S y)
    if PrimeSpectrum.zeroLocus p.asIdeal ∩
          PrimeSpectrum.zeroLocus (completedIdeal S yU : Set (completedLocalRing S yU)) =
        {q | q.asIdeal = completedMaximalIdeal S yU}
    then (a : EInt) < depth + δ
    else (a : EInt) ≤ depth + δ ∨
      (b : EInt) < depth + WithBot.map (WithTop.map Int.ofNat)
        (ringKrullDim (completedLocalRing S yU ⧸ p.asIdeal)) + δ := sorry

/-- A coherent formal module satisfies the strict `(a, b)` depth and dimension inequalities at every completed local prime. -/
def SatisfiesStrictInequalities (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)) (a b : ℤ) : Prop :=
  ∀ y : S.Y, (hy : S.y y ∈ S.U) →
    let yU := closedFiberOpenPoint S y hy
    ∀ p : PrimeSpectrum (completedLocalRing S yU),
        p ∉ PrimeSpectrum.zeroLocus (completedIdeal S yU : Set (completedLocalRing S yU)) →
          let depth : EInt := enatToEInt <|
            moduleDepth (Localization.AtPrime p.asIdeal)
              (LocalizedModule.AtPrime p.asIdeal (completedStalk S F yU))
          let δ : EInt := enatToEInt (algebraizationDistance S y)
          (a : EInt) < depth + δ ∨
            (b : EInt) < depth +
              WithBot.map (WithTop.map Int.ofNat)
                (ringKrullDim (completedLocalRing S yU ⧸ p.asIdeal)) + δ

/-- Applying the strict inequalities at a point gives the corresponding strict alternative. -/
theorem satisfiesStrictInequalities_apply (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)) (a b : ℤ)
    (hF : SatisfiesStrictInequalities S F a b) (y : S.Y) (hy : S.y y ∈ S.U)
    (p : PrimeSpectrum (completedLocalRing S (closedFiberOpenPoint S y hy)))
    (hp : p ∉ PrimeSpectrum.zeroLocus
      (completedIdeal S (closedFiberOpenPoint S y hy) :
        Set (completedLocalRing S (closedFiberOpenPoint S y hy)))) :
    let yU := closedFiberOpenPoint S y hy
    let depth : EInt := enatToEInt <|
      moduleDepth (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal (completedStalk S F yU))
    let δ : EInt := enatToEInt (algebraizationDistance S y)
    (a : EInt) < depth + δ ∨
      (b : EInt) < depth + WithBot.map (WithTop.map Int.ofNat)
        (ringKrullDim (completedLocalRing S yU ⧸ p.asIdeal)) + δ := sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
