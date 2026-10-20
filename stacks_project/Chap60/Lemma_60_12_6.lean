/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap60.Definition_60_11_1_ModuleProperties
public import stacks_project.Chap60.Lemma_60_12_3_Differentials
public import stacks_project.Chap60.«60_9_1_1»

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Crystalline
open CrystallineModuleSheaf
open scoped AlgebraicGeometry

@[expose] public section

universe u

/-- Lemma 60.12.6 (1): in Situation 60.7.5, the crystalline sheaf of
differentials `Ω_{X/S}` is locally quasi-coherent. -/
@[stacks 07KM, instance]
instance crystallineDifferentials_isLocallyQuasiCoherent
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
    (Ω_XS : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p) :
    CrystallineModuleSheaf.IsLocallyQuasiCoherent Ω_XS.module := sorry

/-- Lemma 60.12.6 (2): in Situation 60.7.5, for a morphism of `Cris(X/S)` whose
thickening map `T ⟶ T'` is a closed immersion, the comparison
`c_φ : φ^*(Ω_{X/S})_{T'} ⟶ (Ω_{X/S})_T` is an epimorphism. -/
@[stacks 07KM]
theorem crystallineDifferentials_comparison_epi_of_closedImmersion
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
    (Ω_XS : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (T T' : smallCrystallineSite S I γ h_compatible X x₀)
    (φ : T ⟶ T')
    (h_closed : IsClosedImmersion φ.hom.thickening) :
    Epi (Ω_XS.module.comparison φ.hom) := sorry
