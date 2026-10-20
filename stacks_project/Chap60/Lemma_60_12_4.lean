/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap60.Lemma_60_12_2
public import stacks_project.Chap60.Lemma_60_12_3

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Crystalline
open CrystallineModuleSheaf
open DividedPowerScheme.RelativeDifferentials
open scoped AlgebraicGeometry RelativeDerivation

@[expose] public section

universe u

/-- Lemma 60.12.4: in Situation 60.7.5, for an affine object `(U, T, δ)` of
`Cris(X/S)` mapping into an affine open `V ⊆ S`, global sections of `Ω_{X/S}`
on that object are uniquely identified with the Section 60.6 module
`dividedPowerDifferential` of `Γ(T, 𝒪_T)` over `Γ(V, 𝒪_V)`. -/
@[stacks 07J0]
theorem crystallineDifferentials_affineSections
    (p : ℕ) [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (h_I_quasiCoherent : I.toModule.IsQuasicoherent)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (h_T_quasiCoherent : T.obj.1.ideal.toModule.IsQuasicoherent)
    [IsAffine T.obj.1.thickening]
    (V : S.affineOpens)
    (hTV : (⊤ : T.obj.1.thickening.Opens) ≤ T.obj.1.thickeningToBase ⁻¹ᵁ V.1)
    (Ω_XS : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (D_T : DividedPowerScheme.RelativeDifferentials
      (CrystallineObject.toDividedPowerScheme T.obj.1 h_T_quasiCoherent)
      S T.obj.1.thickeningToBase) :
    let W : T.obj.1.thickening.affineOpens := ⟨⊤, isAffineOpen_top T.obj.1.thickening⟩
    ∃! eΩ : Γ(Ω_XS.module.obj T.obj.1, ⊤) ≃ₗ[Γ(T.obj.1.thickening, ⊤)]
      dividedPowerDifferential
        (T.obj.1.thickeningToBase.appLE V.1 W.1 hTV).hom (T.obj.1.gamma W),
      ∀ a : Γ(T.obj.1.thickening, ⊤),
        eΩ (((Ω_XS.derivation.component T.obj.1).app (op ⊤)).d a) =
          dividedPowerDifferentialDerivation
            (T.obj.1.thickeningToBase.appLE V.1 W.1 hTV).hom (T.obj.1.gamma W) a :=
  sorry

/-- Evaluation of the unique affine-section identification of `Ω_{X/S}` on the
universal crystalline derivation. -/
theorem crystallineDifferentials_affineSections_apply
    (p : ℕ) [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (h_I_quasiCoherent : I.toModule.IsQuasicoherent)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (h_T_quasiCoherent : T.obj.1.ideal.toModule.IsQuasicoherent)
    [IsAffine T.obj.1.thickening]
    (V : S.affineOpens)
    (hTV : (⊤ : T.obj.1.thickening.Opens) ≤ T.obj.1.thickeningToBase ⁻¹ᵁ V.1)
    (Ω_XS : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (D_T : DividedPowerScheme.RelativeDifferentials
      (CrystallineObject.toDividedPowerScheme T.obj.1 h_T_quasiCoherent)
      S T.obj.1.thickeningToBase)
    (a : Γ(T.obj.1.thickening, ⊤)) :
    let W : T.obj.1.thickening.affineOpens := ⟨⊤, isAffineOpen_top T.obj.1.thickening⟩
    ∀ eΩ : Γ(Ω_XS.module.obj T.obj.1, ⊤) ≃ₗ[Γ(T.obj.1.thickening, ⊤)]
      dividedPowerDifferential
        (T.obj.1.thickeningToBase.appLE V.1 W.1 hTV).hom (T.obj.1.gamma W),
      (∀ b : Γ(T.obj.1.thickening, ⊤),
        eΩ (((Ω_XS.derivation.component T.obj.1).app (op ⊤)).d b) =
          dividedPowerDifferentialDerivation
            (T.obj.1.thickeningToBase.appLE V.1 W.1 hTV).hom (T.obj.1.gamma W) b) →
      eΩ (((Ω_XS.derivation.component T.obj.1).app (op ⊤)).d a) =
        dividedPowerDifferentialDerivation
          (T.obj.1.thickeningToBase.appLE V.1 W.1 hTV).hom (T.obj.1.gamma W) a :=
  sorry

