/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Quotient

@[expose] public section

open CategoryTheory

universe u v

namespace CategoryTheory.TwoPeriodicEndomorphism

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

#check (CategoryTheory.TwoPeriodicEndomorphism.ofQuotientComp_le_comap_phi :
  ∀ (φ ψ : Module.End R M),
    (φ.comp ψ).range = (ψ.comp φ).range →
      (φ.comp ψ).range ≤ (φ.comp ψ).range.comap φ)

#check (CategoryTheory.TwoPeriodicEndomorphism.ofQuotientComp_le_comap_psi :
  ∀ (φ ψ : Module.End R M),
    (φ.comp ψ).range = (ψ.comp φ).range →
      (φ.comp ψ).range ≤ (φ.comp ψ).range.comap ψ)

#check (CategoryTheory.TwoPeriodicEndomorphism.ofQuotientComp_d₀_d₁ :
  ∀ (φ ψ : Module.End R M)
    (hRange : (φ.comp ψ).range = (ψ.comp φ).range),
      ModuleCat.ofHom ((φ.comp ψ).range.mapQ (φ.comp ψ).range φ
        (CategoryTheory.TwoPeriodicEndomorphism.ofQuotientComp_le_comap_phi φ ψ hRange)) ≫
          ModuleCat.ofHom ((φ.comp ψ).range.mapQ (φ.comp ψ).range ψ
            (CategoryTheory.TwoPeriodicEndomorphism.ofQuotientComp_le_comap_psi φ ψ hRange)) = 0)

#check (CategoryTheory.TwoPeriodicEndomorphism.ofQuotientComp_d₁_d₀ :
  ∀ (φ ψ : Module.End R M)
    (hRange : (φ.comp ψ).range = (ψ.comp φ).range),
      ModuleCat.ofHom ((φ.comp ψ).range.mapQ (φ.comp ψ).range ψ
        (CategoryTheory.TwoPeriodicEndomorphism.ofQuotientComp_le_comap_psi φ ψ hRange)) ≫
          ModuleCat.ofHom ((φ.comp ψ).range.mapQ (φ.comp ψ).range φ
            (CategoryTheory.TwoPeriodicEndomorphism.ofQuotientComp_le_comap_phi φ ψ hRange)) = 0)

#check (CategoryTheory.TwoPeriodicEndomorphism.ofQuotientComp :
  ∀ (φ ψ : Module.End R M),
    (φ.comp ψ).range = (ψ.comp φ).range →
      CategoryTheory.TwoPeriodicEndomorphism (ModuleCat R))

#check (CategoryTheory.TwoPeriodicEndomorphism.ofQuotientComp_X :
  ∀ (φ ψ : Module.End R M)
    (hRange : (φ.comp ψ).range = (ψ.comp φ).range),
      (CategoryTheory.TwoPeriodicEndomorphism.ofQuotientComp φ ψ hRange).X =
        ModuleCat.of R (M ⧸ (φ.comp ψ).range))

#check (CategoryTheory.TwoPeriodicEndomorphism.ofQuotientComp_d₀_apply_mk :
  ∀ (φ ψ : Module.End R M)
    (hRange : (φ.comp ψ).range = (ψ.comp φ).range) (x : M),
      (CategoryTheory.TwoPeriodicEndomorphism.ofQuotientComp φ ψ hRange).d₀.hom
          (Submodule.Quotient.mk x) =
        Submodule.Quotient.mk (φ x))

#check (CategoryTheory.TwoPeriodicEndomorphism.ofQuotientComp_d₁_apply_mk :
  ∀ (φ ψ : Module.End R M)
    (hRange : (φ.comp ψ).range = (ψ.comp φ).range) (x : M),
      (CategoryTheory.TwoPeriodicEndomorphism.ofQuotientComp φ ψ hRange).d₁.hom
          (Submodule.Quotient.mk x) =
        Submodule.Quotient.mk (ψ x))

#check (CategoryTheory.TwoPeriodicEndomorphism.ofQuotientComp_acyclic_of_injective :
  ∀ (φ ψ : Module.End R M), Function.Injective φ → Function.Injective ψ →
    (hRange : (φ.comp ψ).range = (ψ.comp φ).range) →
      (CategoryTheory.TwoPeriodicEndomorphism.ofQuotientComp φ ψ hRange).toCochainComplex.Acyclic)

#check (CategoryTheory.TwoPeriodicEndomorphism.quotientComp_isFiniteLength :
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {N : Type v} [AddCommGroup N] [Module A N] [Module.Finite A N]
    (φ ψ : Module.End A N), Function.Injective φ → Function.Injective ψ →
      (φ.comp ψ).range = (ψ.comp φ).range → Module.supportDim A N = 1 →
        IsFiniteLength A (N ⧸ (φ.comp ψ).range))

end CategoryTheory.TwoPeriodicEndomorphism
