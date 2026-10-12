/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.RingTheory.KrullDimension.Module
public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic
public import ReasLib.LinearAlgebra.Quotient.Map
public import ReasLib.RingTheory.Module.Support.FiniteLength

/-!
# Two-Periodic Complexes on Quotients by Composite Ranges

This file constructs the two-periodic complex induced by two endomorphisms on the quotient by
the range of their composite.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CategoryTheory.TwoPeriodicEndomorphism

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The range of `φ.comp ψ` is stable under `φ` when the two composite ranges agree. -/
theorem ofQuotientComp_le_comap_phi (φ ψ : Module.End R M)
    (hRange : (φ.comp ψ).range = (ψ.comp φ).range) :
    (φ.comp ψ).range ≤ (φ.comp ψ).range.comap φ := sorry

/-- The range of `φ.comp ψ` is stable under `ψ` when the two composite ranges agree. -/
theorem ofQuotientComp_le_comap_psi (φ ψ : Module.End R M)
    (hRange : (φ.comp ψ).range = (ψ.comp φ).range) :
    (φ.comp ψ).range ≤ (φ.comp ψ).range.comap ψ := sorry

/-- The maps induced by `φ` and `ψ` on the quotient by `range (φ.comp ψ)` compose to zero. -/
theorem ofQuotientComp_d₀_d₁ (φ ψ : Module.End R M)
    (hRange : (φ.comp ψ).range = (ψ.comp φ).range) :
    ModuleCat.ofHom ((φ.comp ψ).range.mapQ (φ.comp ψ).range φ
      (ofQuotientComp_le_comap_phi φ ψ hRange)) ≫
        ModuleCat.ofHom ((φ.comp ψ).range.mapQ (φ.comp ψ).range ψ
          (ofQuotientComp_le_comap_psi φ ψ hRange)) = 0 := sorry

/-- The maps induced by `ψ` and `φ` on the quotient by `range (φ.comp ψ)` compose to zero. -/
theorem ofQuotientComp_d₁_d₀ (φ ψ : Module.End R M)
    (hRange : (φ.comp ψ).range = (ψ.comp φ).range) :
    ModuleCat.ofHom ((φ.comp ψ).range.mapQ (φ.comp ψ).range ψ
      (ofQuotientComp_le_comap_psi φ ψ hRange)) ≫
        ModuleCat.ofHom ((φ.comp ψ).range.mapQ (φ.comp ψ).range φ
          (ofQuotientComp_le_comap_phi φ ψ hRange)) = 0 := sorry

/-- The two-periodic endomorphism complex induced by `φ` and `ψ` on
`M ⧸ range (φ.comp ψ)`. -/
def ofQuotientComp (φ ψ : Module.End R M)
    (hRange : (φ.comp ψ).range = (ψ.comp φ).range) :
    TwoPeriodicEndomorphism (ModuleCat R) where
  X := ModuleCat.of R (M ⧸ (φ.comp ψ).range)
  d₀ := ModuleCat.ofHom ((φ.comp ψ).range.mapQ (φ.comp ψ).range φ
    (ofQuotientComp_le_comap_phi φ ψ hRange))
  d₁ := ModuleCat.ofHom ((φ.comp ψ).range.mapQ (φ.comp ψ).range ψ
    (ofQuotientComp_le_comap_psi φ ψ hRange))
  d₀_d₁ := ofQuotientComp_d₀_d₁ φ ψ hRange
  d₁_d₀ := ofQuotientComp_d₁_d₀ φ ψ hRange

/-- The object underlying `ofQuotientComp φ ψ hRange` is the quotient by
`range (φ.comp ψ)`. -/
@[simp]
theorem ofQuotientComp_X (φ ψ : Module.End R M)
    (hRange : (φ.comp ψ).range = (ψ.comp φ).range) :
    (ofQuotientComp φ ψ hRange).X = ModuleCat.of R (M ⧸ (φ.comp ψ).range) := sorry

/-- On quotient representatives, the degree-zero differential of `ofQuotientComp` is `φ`. -/
@[simp]
theorem ofQuotientComp_d₀_apply_mk (φ ψ : Module.End R M)
    (hRange : (φ.comp ψ).range = (ψ.comp φ).range) (x : M) :
    (ofQuotientComp φ ψ hRange).d₀.hom (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (φ x) := sorry

/-- On quotient representatives, the degree-one differential of `ofQuotientComp` is `ψ`. -/
@[simp]
theorem ofQuotientComp_d₁_apply_mk (φ ψ : Module.End R M)
    (hRange : (φ.comp ψ).range = (ψ.comp φ).range) (x : M) :
    (ofQuotientComp φ ψ hRange).d₁.hom (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (ψ x) := sorry

/-- Injectivity of both endomorphisms makes the quotient two-periodic complex acyclic. -/
theorem ofQuotientComp_acyclic_of_injective (φ ψ : Module.End R M)
    (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    (hRange : (φ.comp ψ).range = (ψ.comp φ).range) :
    (ofQuotientComp φ ψ hRange).toCochainComplex.Acyclic := sorry

/-- Over a Noetherian local ring, the dimension-one hypotheses make the quotient by the
composite range a finite-length module. -/
theorem quotientComp_isFiniteLength {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] {N : Type v} [AddCommGroup N] [Module A N] [Module.Finite A N]
    (φ ψ : Module.End A N) (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    (hRange : (φ.comp ψ).range = (ψ.comp φ).range)
    (hdim : Module.supportDim A N = 1) :
    IsFiniteLength A (N ⧸ (φ.comp ψ).range) := sorry

/-- Under the finite dimension-one local hypotheses, the quotient by the composite range has
module length strictly below `⊤`. -/
theorem quotientComp_length_lt_top {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (φ ψ : Module.End A M) (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    (hRange : (φ.comp ψ).range = (ψ.comp φ).range)
    (hdim : Module.supportDim A M = 1) :
    Module.length A (M ⧸ (φ.comp ψ).range) < ⊤ := sorry

/-- Under the finite dimension-one local hypotheses, the quotient complex induced by two
injective endomorphisms with equal composite ranges is acyclic. -/
theorem quotientComp_acyclic {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (φ ψ : Module.End A M) (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    (hRange : (φ.comp ψ).range = (ψ.comp φ).range)
    (hdim : Module.supportDim A M = 1) :
    (ofQuotientComp φ ψ hRange).toCochainComplex.Acyclic := sorry

end CategoryTheory.TwoPeriodicEndomorphism
