/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ReasLib.RingTheory.AdicCompletion.LocalizationAway
public import ReasLib.RingTheory.AdicCompletion.Map

/-!
# Maps of completed principal localizations

A ring homomorphism `φ : A →+* B` induces
`completedPrincipalLocalization.map φ I f : A_{{f}} →+* B_{{φ f}}` by completing
`Localization.awayMap φ f` along the extended ideals of `I` and `I.map φ`.
-/

@[expose] public section

noncomputable section

universe u v

open AdicCompletion

namespace completedPrincipalLocalization

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- Powers of the extended ideal of `I` along `Localization.Away f` are contained
in the comap of the corresponding powers of the extended ideal of `I.map φ`
along `Localization.Away (φ f)`, under `Localization.awayMap φ f`. -/
theorem awayMap_pow_le_comap (φ : A →+* B) (I : Ideal A) (f : A) (n : ℕ) :
    (I.map (algebraMap A (Localization.Away f))) ^ n ≤
      (((I.map φ).map (algebraMap B (Localization.Away (φ f)))) ^ n).comap
        (Localization.awayMap φ f) :=
  sorry

/-- The finite-level quotient map of `Localization.awayMap φ f` after evaluating
the source completed principal localization modulo the `n`-th power of the
extended ideal. -/
def mapQuotient (φ : A →+* B) (I : Ideal A) (f : A) (n : ℕ) :
    completedPrincipalLocalization I f →+*
      Localization.Away (φ f) ⧸
        ((I.map φ).map (algebraMap B (Localization.Away (φ f)))) ^ n :=
  (Ideal.quotientMap
      (((I.map φ).map (algebraMap B (Localization.Away (φ f)))) ^ n)
      (Localization.awayMap φ f) (awayMap_pow_le_comap φ I f n)).comp
    (evalₐ (I.map (algebraMap A (Localization.Away f))) n)

/-- The finite-level maps `mapQuotient` are compatible with the inverse-system
transition maps. -/
theorem mapQuotient_compatible (φ : A →+* B) (I : Ideal A) (f : A)
    {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow
        ((I.map φ).map (algebraMap B (Localization.Away (φ f)))) hle).comp
      (mapQuotient φ I f n) =
      mapQuotient φ I f m :=
  sorry

/-- The ring homomorphism `A_{{f}} →+* B_{{φ f}}` obtained by completing
`Localization.awayMap φ f` along the extended ideals of `I` and `I.map φ`. -/
def map (φ : A →+* B) (I : Ideal A) (f : A) :
    completedPrincipalLocalization I f →+* completedPrincipalLocalization (I.map φ) (φ f) :=
  liftRingHom ((I.map φ).map (algebraMap B (Localization.Away (φ f))))
    (mapQuotient φ I f) (fun hle ↦ mapQuotient_compatible φ I f hle)

/-- Evaluating `map φ I f` at the `n`-th finite quotient recovers `mapQuotient`. -/
theorem map_eval (φ : A →+* B) (I : Ideal A) (f : A) (n : ℕ) :
    (evalₐ ((I.map φ).map (algebraMap B (Localization.Away (φ f)))) n).toRingHom.comp
        (map φ I f) =
      mapQuotient φ I f n :=
  sorry

/-- The induced map on principal localizations is adically continuous for the
extended ideals. -/
theorem awayMap_adicContinuous (φ : A →+* B) (I : Ideal A) (f : A) :
    (Localization.awayMap φ f).AdicContinuous
      (I.map (algebraMap A (Localization.Away f)))
      ((I.map φ).map (algebraMap B (Localization.Away (φ f)))) :=
  RingHom.AdicContinuous.of_map_le <| by
    rw [Ideal.map_map, Ideal.map_map]
    have hcomp :
        (Localization.awayMap φ f).comp (algebraMap A (Localization.Away f)) =
          (algebraMap B (Localization.Away (φ f))).comp φ := by
      ext a
      simp [Localization.awayMap, IsLocalization.Away.map]
    rw [hcomp]

/-- `map` is the completion map of `awayMap_adicContinuous`. -/
theorem map_eq (φ : A →+* B) (I : Ideal A) (f : A) :
    map φ I f =
      RingHom.AdicContinuous.completionMap (awayMap_adicContinuous φ I f) :=
  sorry

/-- `map` extends `Localization.awayMap` through the canonical maps from
principal localizations. -/
theorem map_comp_away (φ : A →+* B) (I : Ideal A) (f : A) :
    (map φ I f).comp (ofAway I f) =
      (ofAway (I.map φ) (φ f)).comp (Localization.awayMap φ f) :=
  sorry

/-- `map` extends `φ` through the canonical maps from `A` and `B`. -/
theorem map_comp (φ : A →+* B) (I : Ideal A) (f : A) :
    (map φ I f).comp (of I f) = (of (I.map φ) (φ f)).comp φ :=
  sorry

end completedPrincipalLocalization

