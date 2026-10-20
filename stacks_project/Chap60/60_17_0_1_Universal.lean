/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DividedPowers.Envelope.Universal

@[expose] public section

universe u

variable {A B : Type u} [CommRing A] [CommRing B]
  {I : Ideal A} (γ : DividedPowers I) (f : A →+* B)
  {J : Ideal B} (hIJ : Ideal.map f I ≤ J)
  (E : DividedPowerEnvelope I γ f J hIJ)

/- The universal mapping-property specification for a divided-power envelope. -/
#check (DividedPowerEnvelope.IsUniversal γ f hIJ E : Prop)

/- The unfolding theorem for the universal mapping-property specification. -/
#check (DividedPowerEnvelope.IsUniversal_def γ f hIJ E :
  DividedPowerEnvelope.IsUniversal γ f hIJ E ↔
    ∀ {T : DividedPowerRing.{u}} (φ : B →+* T),
      DividedPowers.IsDPMorphism γ T.dividedPowers (φ.comp f) →
      Ideal.map φ J ≤ T.ideal →
      ∃! ψ : E.D ⟶ T, ψ.toRingHom.comp E.toD = φ)
