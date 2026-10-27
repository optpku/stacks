/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Relative
public import ReasLib.AlgebraicGeometry.Crystalline.Functoriality
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open Scheme.IdealSheafData

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Crystalline.Frobenius

variable {p : ℕ} [Fact p.Prime]

/-- Local nilpotence of the prime is preserved by the Frobenius twist over
a characteristic-p base. -/
theorem twistPrimeNilpotent {X S₀ : Scheme.{u}} [Scheme.IsCharP S₀ p]
    (x₀ : X ⟶ S₀) (hp : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U))) :
    ∀ U : (relativeFrobeniusTarget (p := p) x₀).affineOpens,
      IsNilpotent (p : Γ(relativeFrobeniusTarget (p := p) x₀, U)) := sorry

variable {A : Type u} [CommRing A]
variable (I : (Spec (.of A)).IdealSheafData)
variable (s : Spec (.of A) ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (σ : A →+* A)
variable (h_ideal : I.comap (Spec.map (CommRingCat.ofHom σ)) ≤ I)
variable (h_over : Spec.map (CommRingCat.ofHom σ) ≫ s = s)

/-- An affine endomorphism preserving the defining ideal and the prime-local
base induces a morphism of divided-power scheme setups. -/
def specSigmaHom : DividedPowerSchemeHom I I s s where
  base := Spec.map (CommRingCat.ofHom σ)
  zeroFiberMap := subschemeMap I I (Spec.map (CommRingCat.ofHom σ))
    (le_map_iff_comap_le.mpr h_ideal)
  zeroFiber_comm := subschemeMap_subschemeι I I (Spec.map (CommRingCat.ofHom σ))
    (le_map_iff_comap_le.mpr h_ideal)
  base_over := h_over
  ideal_compatible := h_ideal

variable [h_quasicoherent : I.toModule.IsQuasicoherent] [Scheme.IsCharP I.subscheme p]
variable (h_p_mem : ∀ V : (Spec (.of A)).affineOpens, (p : Γ(Spec (.of A), V)) ∈ I.ideal V)
variable (h_sigma : ∀ a : A, σ a - a ^ p ∈ Ideal.span ({(p : A)} : Set A))

include h_quasicoherent h_p_mem h_sigma in
/-- An affine Frobenius lift induces absolute Frobenius on the closed fibre
when its quasi-coherent defining ideal contains the prime. -/
theorem sigmaZeroFiber_eq_frobenius :
    (specSigmaHom I s σ h_ideal h_over).zeroFiberMap =
      Scheme.absoluteFrobenius p I.subscheme := sorry

include h_quasicoherent h_p_mem h_sigma in
/-- The first projection of the Frobenius twist lies over the closed-fibre
map of the given affine Frobenius lift. -/
theorem twist_over_specSigma {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme) :
    pullback.fst x₀ (Scheme.absoluteFrobenius p I.subscheme) ≫ x₀ =
      pullback.snd x₀ (Scheme.absoluteFrobenius p I.subscheme) ≫
        (specSigmaHom I s σ h_ideal h_over).zeroFiberMap := sorry

end AlgebraicGeometry.Scheme.Crystalline.Frobenius
