/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.Crystalline.Connection.Affine

@[expose] public section
open AlgebraicGeometry CategoryTheory KaehlerDifferential.DeRham
universe u

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable {J : Ideal B} (δ : DividedPowers J)
variable [Module Bᵐᵒᵖ (ambientDividedPowerDifferential (A := A) (B := B) δ)]
variable [IsCentralScalar B (ambientDividedPowerDifferential (A := A) (B := B) δ)]

variable {S X : Scheme.{u}} (I : S.IdealSheafData)
variable (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
variable (hc : ∀ (V : S.affineOpens) (a : Γ(S, V)),
  (γ V).IsDPMorphism (γ (S.affineBasicOpen a))
    (S.presheaf.map (homOfLE (S.basicOpen_le a)).op).hom)
variable (x₀ : X ⟶ I.subscheme)
variable (base : Spec (.of B) ⟶ S) (fibre : Spec (.of (B ⧸ J)) ⟶ X)
variable (comm : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ base =
  fibre ≫ x₀ ≫ I.subschemeι)

variable (hJ : ∀ x ∈ J, IsNilpotent x)
variable (hrelative : CrystallineBaseCompatible I γ hc x₀
  (CechCrisCover.affineCrystallineObject I γ hc x₀ J δ hJ base fibre comm))
variable (hopen : IsOpenImmersion fibre)

variable (hbase : Spec.map (CommRingCat.ofHom (CrystallinePDDeRham.differentialLift A B δ)) ≫
  base = CrystallinePDSquareZeroGeometry.extendedBase A B δ base)

variable (F : CrystallineModuleSheaf.CrisModuleSheaf S I γ hc X x₀)
variable [CrystallineCoefficients.SectionsCoherent I γ hc x₀ F]
variable [CrystallineModuleSheaf.CrisModuleSheaf.IsCrystal F]
variable [CrystallineModuleSheaf.CrisModuleSheaf.IsLocallyQuasiCoherent F]

#check (CrystallinePDSquareZeroGeometry.connection A B δ I γ hc x₀ base fibre comm
    hJ hrelative hopen hbase F :
  Connection (ambientDividedPowerDifferentialDerivation (A := A) δ)
    (CrystallinePDSquareZeroGeometry.coefficientModule B δ I γ hc x₀ base fibre comm
      hJ hrelative hopen F))
