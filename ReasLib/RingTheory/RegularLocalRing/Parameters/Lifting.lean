/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.RegularLocalRing.Parameters.Properties
public import ReasLib.RingTheory.Sequence.Annihilator

@[expose] public section

/-!
# Lifting regular parameters from a prime localization

The main theorem combines denominator clearing for a regular system of
parameters with successive annihilator stabilization.  The powered-prefix
condition is exposed through `RingTheory.Sequence.StableAnnihilators`.
-/

universe u

open IsLocalRing

namespace PrimeSpectrum

variable {Λ : Type u} [CommRing Λ]

namespace Parameters

/-- A lift to `Λ` of a regular parameter family at `q`, with prescribed
power containment and stable successive annihilators.  The number of
parameters belongs to the lift rather than to its ambient setup. -/
@[stacks 07FD]
structure Lift (q : PrimeSpectrum Λ) (I : Ideal Λ) (n e : ℕ+) where
  /-- The number of lifted parameters. -/
  length : ℕ
  /-- The lifted parameter family in the original ring. -/
  elements : Fin length → Λ
  /-- Each lifted parameter maps into the maximal ideal at `q`. -/
  memMaximal : ∀ i,
    algebraMap Λ (Localization.AtPrime q.asIdeal) (elements i) ∈
      maximalIdeal (Localization.AtPrime q.asIdeal)
  /-- The localized lifted elements form a regular system of parameters. -/
  regular : IsRegularSystemOfParameters
    (fun i ↦
      (⟨algebraMap Λ (Localization.AtPrime q.asIdeal) (elements i), memMaximal i⟩ :
        maximalIdeal (Localization.AtPrime q.asIdeal)))
  /-- The prescribed positive powers of the lifted parameters lie in `I`. -/
  powMem : ∀ i, elements i ^ (n : ℕ) ∈ I
  /-- Successive annihilators stabilize modulo preceding `e`-th powers. -/
  stable : RingTheory.Sequence.StableAnnihilators elements (e : ℕ)

namespace Lift

/-- Construct a lifted regular parameter family from its defining data. -/
def of {q : PrimeSpectrum Λ} {I : Ideal Λ} {n e : ℕ+} {d : ℕ}
    (elements : Fin d → Λ)
    (memMaximal : ∀ i,
      algebraMap Λ (Localization.AtPrime q.asIdeal) (elements i) ∈
        maximalIdeal (Localization.AtPrime q.asIdeal))
    (regular : IsRegularSystemOfParameters
      (fun i ↦
        (⟨algebraMap Λ (Localization.AtPrime q.asIdeal) (elements i), memMaximal i⟩ :
          maximalIdeal (Localization.AtPrime q.asIdeal))))
    (powMem : ∀ i, elements i ^ (n : ℕ) ∈ I)
    (stable : RingTheory.Sequence.StableAnnihilators elements (e : ℕ)) :
    Lift q I n e where
  length := d
  elements := elements
  memMaximal := memMaximal
  regular := regular
  powMem := powMem
  stable := stable

/-- The constructor records the index length supplied by its parameter family. -/
@[simp]
theorem length_of {q : PrimeSpectrum Λ} {I : Ideal Λ} {n e : ℕ+} {d : ℕ}
    (elements : Fin d → Λ)
    (memMaximal : ∀ i,
      algebraMap Λ (Localization.AtPrime q.asIdeal) (elements i) ∈
        maximalIdeal (Localization.AtPrime q.asIdeal))
    (regular : IsRegularSystemOfParameters
      (fun i ↦
        (⟨algebraMap Λ (Localization.AtPrime q.asIdeal) (elements i), memMaximal i⟩ :
          maximalIdeal (Localization.AtPrime q.asIdeal))))
    (powMem : ∀ i, elements i ^ (n : ℕ) ∈ I)
    (stable : RingTheory.Sequence.StableAnnihilators elements (e : ℕ)) :
    (of elements memMaximal regular powMem stable).length = d := sorry

/-- The localized lift, regarded as a family in the maximal ideal at `q`. -/
def localized {q : PrimeSpectrum Λ} {I : Ideal Λ} {n e : ℕ+}
    (L : Lift q I n e) :
    Fin L.length → maximalIdeal (Localization.AtPrime q.asIdeal) :=
  fun i ↦ ⟨algebraMap Λ (Localization.AtPrime q.asIdeal) (L.elements i), L.memMaximal i⟩

/-- Coercing a localized lift recovers the image of the original lifted element. -/
@[simp]
theorem localized_apply {q : PrimeSpectrum Λ} {I : Ideal Λ} {n e : ℕ+}
    (L : Lift q I n e) (i : Fin L.length) :
    (L.localized i : Localization.AtPrime q.asIdeal) =
      algebraMap Λ (Localization.AtPrime q.asIdeal) (L.elements i) := sorry

/-- The localized family attached to a lift is a regular system of parameters. -/
theorem isRegular {q : PrimeSpectrum Λ} {I : Ideal Λ} {n e : ℕ+}
    (L : Lift q I n e) : IsRegularSystemOfParameters L.localized := sorry

/-- The defining properties of a lifted regular parameter family. -/
theorem spec {q : PrimeSpectrum Λ} {I : Ideal Λ} {n e : ℕ+}
    (L : Lift q I n e) :
    (∀ i,
      algebraMap Λ (Localization.AtPrime q.asIdeal) (L.elements i) ∈
        maximalIdeal (Localization.AtPrime q.asIdeal)) ∧
      IsRegularSystemOfParameters L.localized ∧
      (∀ i, L.elements i ^ (n : ℕ) ∈ I) ∧
      RingTheory.Sequence.StableAnnihilators L.elements (e : ℕ) := sorry

/-- A regular localization admits a lifted parameter family when the prescribed
ideal contains a positive power of the local maximal ideal. -/
@[stacks 07FD "lifted parameters from local maximal-ideal power containment"]
theorem nonempty
    (q : PrimeSpectrum Λ) [IsNoetherianRing Λ]
    (I : Ideal Λ) (n e : ℕ+)
    (hqpow :
      maximalIdeal (Localization.AtPrime q.asIdeal) ^ (n : ℕ) ≤
        Ideal.map (algebraMap Λ (Localization.AtPrime q.asIdeal)) I)
    [IsRegularLocalRing (Localization.AtPrime q.asIdeal)] :
    Nonempty (Lift q I n e) := sorry

/-- Lemma 16.10.2 (Tag 07FD): positive powers of a regular parameter family
can be lifted from `Λ_q`, arranged to lie in a prescribed ideal, and
rescaled so that all successive annihilators stabilize; when the dimension is
`d`, the chosen family has exactly `d` entries. -/
@[stacks 07FD]
theorem nonempty_of_dimension
    (q : PrimeSpectrum Λ) [IsNoetherianRing Λ]
    (I : Ideal Λ) (n e : ℕ+) {d : ℕ}
    (hIq : I ≤ q.asIdeal)
    (hqpow :
      Ideal.map (algebraMap Λ (Localization.AtPrime q.asIdeal))
          (q.asIdeal ^ (n : ℕ)) ≤
        Ideal.map (algebraMap Λ (Localization.AtPrime q.asIdeal)) I)
    [IsRegularLocalRing (Localization.AtPrime q.asIdeal)]
    (hdim : ringKrullDim (Localization.AtPrime q.asIdeal) = d) :
    Nonempty {L : Lift q I n e // L.length = d} := sorry

end Lift

end Parameters

end PrimeSpectrum
