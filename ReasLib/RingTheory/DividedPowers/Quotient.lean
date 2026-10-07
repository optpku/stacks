module

public import Mathlib.RingTheory.DividedPowers.SubDPIdeal
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.DividedPowers.Extension

@[expose] public section

/-!
# Quotients of Divided-Power Ideals

This module relates sub-divided-power ideals to extension of divided powers along quotient maps.
-/

universe u

namespace DividedPowers

variable {A : Type u} [CommRing A] {I : Ideal A}

/-- The intersection of an ideal with a divided-power ideal is
sub-divided-power exactly when the divided powers extend along the quotient map. -/
@[stacks 07H2 "(2)"]
theorem isSubDPIdeal_inf_iff_extendsAlong_quotientMk (γ : DividedPowers I) (𝔞 : Ideal A) :
    IsSubDPIdeal γ (𝔞 ⊓ I) ↔ γ.extendsAlong (Ideal.Quotient.mk 𝔞) := sorry

/-- The quotient-map extension criterion expanded into an explicit target divided-power
structure and divided-power morphism. -/
theorem isSubDPIdeal_inf_iff_exists_quotientDividedPowers
    (γ : DividedPowers I) (𝔞 : Ideal A) :
    IsSubDPIdeal γ (𝔞 ⊓ I) ↔
      ∃ γq : DividedPowers (I.map (Ideal.Quotient.mk 𝔞)),
        IsDPMorphism γ γq (Ideal.Quotient.mk 𝔞) := sorry

/-- A span presentation of the intersection ideal gives an elementwise criterion for it to be
a sub-divided-power ideal. -/
theorem isSubDPIdeal_inf_iff_span_eq (γ : DividedPowers I) {𝔞 : Ideal A} {S : Set A}
    (hS : Ideal.span S = 𝔞 ⊓ I) :
    IsSubDPIdeal γ (𝔞 ⊓ I) ↔
      ∀ n : ℕ, n ≠ 0 → ∀ s : A, s ∈ S → γ.dpow n s ∈ Ideal.span S := sorry

/-- The intersection of an ideal with a divided-power ideal is
sub-divided-power exactly when it has a generating set stable under positive divided powers. -/
@[stacks 07H2]
theorem isSubDPIdeal_inf_iff_exists_generatingSet (γ : DividedPowers I) (𝔞 : Ideal A) :
    IsSubDPIdeal γ (𝔞 ⊓ I) ↔
      ∃ S : Set A,
        Ideal.span S = 𝔞 ⊓ I ∧
          ∀ n : ℕ, n ≠ 0 → ∀ s : A, s ∈ S → γ.dpow n s ∈ Ideal.span S := sorry

end DividedPowers
