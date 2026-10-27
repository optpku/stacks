/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.RingTheory.DividedPowers.CrystallineCompletion
public import ReasLib.RingTheory.AdicCompletion.PrimeLocal


@[expose] public section

open CategoryTheory CategoryTheory.Limits DividedPowers

universe u

namespace DividedPowers.PadicBase

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable [IsAdicComplete (Ideal.span {(p : A)}) A]
variable {I : Ideal A} (γ : DividedPowers I)
variable (hp : IsNilpotent (Ideal.Quotient.mk I (p : A)))


include hp in
/-- The image of the integer prime is nilpotent in the closed fibre ring. -/
theorem quotientPrimeNilpotent : IsNilpotent (p : A ⧸ I) := by
  simpa using hp

/-- The complete base itself as a completed crystalline object over its closed fibre.
Both ring maps are fixed: identity on A, and the quotient A → A/I. -/
noncomputable def completedBase :
    CompletedCrisObject p A I γ (A ⧸ I) (Ideal.Quotient.mk I)
      (Ideal.map_quotient_self I) (quotientPrimeNilpotent hp) :=
  CompletedCrisObject.of γ (Ideal.Quotient.mk I)
    (Ideal.map_quotient_self I) (quotientPrimeNilpotent hp)
    (DividedPowerRing.of A I γ) (DPMorphism.id γ) (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective Ideal.mk_ker (RingHom.comp_id _)
    (inferInstance : IsAdicComplete (Ideal.span {(p : A)}) A)

/-- A cofinal offset for which all powers of p lie in I and are PD-stable. -/
noncomputable def offset : ℕ :=
  pAdicOffset γ (Ideal.Quotient.mk I) (Ideal.map_quotient_self I)
    (quotientPrimeNilpotent hp) (completedBase γ hp)

/-- The offset retains both the closed-fibre inclusion and PD stability. -/
theorem offset_spec :
    Ideal.span {(p : A)} ^ offset γ hp ≤ I ∧
      IsStableUnderPowers γ (Ideal.span {(p : A)}) (offset γ hp) := sorry

/-- The exponent at index e is e plus a fixed cofinal offset. -/
noncomputable def exponent (e : ℕ) : ℕ := e + offset γ hp

/-- The shifted prime-power exponents are cofinal in the natural numbers. -/
theorem exponent_cofinal : ∀ n : ℕ, ∃ e : ℕ, n ≤ exponent γ hp e := sorry

/-- The actual quotient PD ring on the cofinal tail, with descended base divided powers. -/
noncomputable def stageRing (e : ℕ) : DividedPowerRing.{u} :=
  pAdicQuotientRing γ (Ideal.Quotient.mk I) (Ideal.map_quotient_self I)
    (quotientPrimeNilpotent hp) (completedBase γ hp) e

/-- The stage carrier is the quotient by the specified ideal power. -/
theorem stageRing_carrier (e : ℕ) :
    (stageRing γ hp e).carrier = (A ⧸ (Ideal.span {(p : A)} ^ exponent γ hp e)) := rfl

/-- The quotient map is a PD map, not an unsupported smooth-extension from A. -/
noncomputable def quotient (e : ℕ) : DPMorphism γ (stageRing γ hp e).dividedPowers :=
  pAdicQuotientMk γ (Ideal.Quotient.mk I) (Ideal.map_quotient_self I)
    (quotientPrimeNilpotent hp) (completedBase γ hp) e

/-- The cofinal quotient still surjects onto the original closed fibre A/I. -/
noncomputable def toClosedFibre (e : ℕ) : stageRing γ hp e →+* A ⧸ I :=
  pAdicQuotientToC γ (Ideal.Quotient.mk I) (Ideal.map_quotient_self I)
    (quotientPrimeNilpotent hp) (completedBase γ hp) e

/-- The original quotient factors through each cofinal PD quotient. -/
theorem toClosedFibre_comp (e : ℕ) :
    (toClosedFibre γ hp e).comp (quotient γ hp e).toRingHom = Ideal.Quotient.mk I := sorry

/-- The prime is nilpotent in each of the genuine quotient rings. -/
theorem stagePrimeNilpotent (e : ℕ) : IsNilpotent (p : stageRing γ hp e) := sorry

/-- Each tail ideal is contained in the ideal of the original closed fibre. -/
theorem power_le (e : ℕ) : Ideal.span {(p : A)} ^ exponent γ hp e ≤ I := sorry

/-- Canonical quotient transition, preserving the descended PD structures. -/
noncomputable def step (e : ℕ) :
    DPMorphism (stageRing γ hp (e + 1)).dividedPowers (stageRing γ hp e).dividedPowers :=
  (pAdicQuotientStep γ (Ideal.Quotient.mk I) (Ideal.map_quotient_self I)
    (quotientPrimeNilpotent hp) (completedBase γ hp) e).hom.map

/-- The transition is compatible with the map out of the complete base. -/
theorem step_comp_quotient (e : ℕ) :
    (step γ hp e).toRingHom.comp (quotient γ hp (e + 1)).toRingHom =
      (quotient γ hp e).toRingHom := sorry

end DividedPowers.PadicBase
