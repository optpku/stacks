/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Frobenius
public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Absolute
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.IdealSheafData

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Crystalline.FrobeniusBase

variable {p : ℕ} [Fact p.Prime] {A : DividedPowerRing.{u}} (B : FrobeniusBase p A)

/-- The chosen divided-power Frobenius lift induces an endomorphism of the affine base. -/
def sigmaMap : B.toBase.scheme ⟶ B.toBase.scheme :=
  eqToHom B.scheme_eq ≫ Spec.map (CommRingCat.ofHom B.sigma.toRingHom) ≫
    eqToHom B.scheme_eq.symm

/-- The affine Frobenius lift preserves the distinguished ideal sheaf. -/
theorem sigmaMap_preservesIdeal :
    B.toBase.ideal.comap (sigmaMap B) ≤ B.toBase.ideal := sorry

/-- The affine Frobenius lift induces an endomorphism of the closed fibre. -/
def sigmaZeroFiber : B.toBase.ideal.subscheme ⟶ B.toBase.ideal.subscheme :=
  subschemeMap B.toBase.ideal B.toBase.ideal (sigmaMap B)
    (le_map_iff_comap_le.mpr (sigmaMap_preservesIdeal B))

/-- The affine Frobenius lift is a morphism over the prime-local integers. -/
theorem sigmaMap_over : sigmaMap B ≫ B.toBase.toSpec = B.toBase.toSpec := sorry

/-- A scheme over the distinguished closed fibre has characteristic `p`. -/
theorem source_char : Scheme.IsCharP B.toBase.source p := sorry

/-- Absolute Frobenius on the source is defined using its closed-fibre characteristic. -/
def sourceFrobenius : B.toBase.source ⟶ B.toBase.source :=
  @Scheme.absoluteFrobenius p inferInstance B.toBase.source (source_char B)

/-- Absolute Frobenius on the source lies over the closed-fibre endomorphism of the lift. -/
theorem absoluteFrobenius_over_sigma :
    sourceFrobenius B ≫ B.toBase.sourceToClosed =
      B.toBase.sourceToClosed ≫ sigmaZeroFiber B := sorry

/-- The affine Frobenius lift preserves divided powers on affine sections. -/
theorem sigma_dividedPowers :
    ∀ (V W : B.toBase.scheme.affineOpens) (hVW : W.1 ≤ sigmaMap B ⁻¹ᵁ V.1),
      (B.toBase.dividedPowers V).IsDPMorphism (B.toBase.dividedPowers W)
        ((sigmaMap B).appLE V W hVW).hom := sorry

end AlgebraicGeometry.Scheme.Crystalline.FrobeniusBase
