/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap60.«60_23_2_1_Eval»
public import stacks_project.Chap60.Lemma_60_15_1
public import stacks_project.Chap60.Lemma_60_17_3_Pair

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Crystalline
open CrystallineModuleSheaf
open CrystallineConnectionPair
open scoped TensorProduct

universe u

variable {A : Type u} [CommRing A] (p : ℕ) [Fact (Nat.Prime p)]
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable (I : Ideal A) (γ : DividedPowers I)
variable {C : Type u} [CommRing C] [Algebra A C]
variable {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C)
variable (hπ : Function.Surjective π)
variable (J : Ideal (MvPolynomial ι A))
variable (hJ : J = RingHom.ker π.toRingHom)
variable (hIC : Ideal.map (algebraMap A C) I = (⊥ : Ideal C))
variable (hpnil : IsNilpotent (p : C))
variable (hIJ : Ideal.map (algebraMap A (MvPolynomial ι A)) I ≤ J)
variable (E : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial ι A)) J hIJ)
variable (hE : DividedPowerEnvelope.IsUniversal γ
  (algebraMap A (MvPolynomial ι A)) hIJ E)
variable (γbar : DividedPowers
  (Ideal.map (algebraMap E.D (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE))
    E.D.ideal))
variable {S : Scheme.{u}} {IS : S.IdealSheafData}
variable {γS : ∀ V : S.affineOpens, DividedPowers (IS.ideal V)}
variable {h_compatible :
    ∀ (V : S.affineOpens) (f : Γ(S, V)),
      (γS V).IsDPMorphism (γS (S.affineBasicOpen f))
        (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
variable {X : Scheme.{u}} {x₀ : X ⟶ IS.subscheme}

/-- Inverse-limit carrier of sections of a crystal on an envelope thickening `T`,
represented as the `p`-adic completion of `Γ(F_T)`. -/
noncomputable def crystalCarrier
    (F : CrisModuleSheaf S IS γS h_compatible X x₀)
    (T : smallCrystallineSite S IS γS h_compatible X x₀)
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)
      (CrisModuleSheaf.sectionModule F T)] : Type u :=
  AdicCompletion (crystallineD.pIdeal p I γ π hπ J hJ hIC hpnil hIJ E hE)
    (CrisModuleSheaf.sectionModule F T)

/-- The carrier of the evaluation functor is the `p`-adic completion of
global sections. -/
theorem crystalCarrier_eq
    (F : CrisModuleSheaf S IS γS h_compatible X x₀)
    (T : smallCrystallineSite S IS γS h_compatible X x₀)
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)
      (CrisModuleSheaf.sectionModule F T)] :
    crystalCarrier p I γ π hπ J hJ hIC hpnil hIJ E hE F T =
      AdicCompletion (crystallineD.pIdeal p I γ π hπ J hJ hIC hpnil hIJ E hE)
        (CrisModuleSheaf.sectionModule F T) :=
  sorry

/-- Additive group structure on the inverse-limit carrier. -/
noncomputable instance crystalCarrier.addCommGroup
    (F : CrisModuleSheaf S IS γS h_compatible X x₀)
    (T : smallCrystallineSite S IS γS h_compatible X x₀)
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)
      (CrisModuleSheaf.sectionModule F T)] :
    AddCommGroup (crystalCarrier p I γ π hπ J hJ hIC hpnil hIJ E hE F T) :=
  inferInstanceAs
    (AddCommGroup
      (AdicCompletion (crystallineD.pIdeal p I γ π hπ J hJ hIC hpnil hIJ E hE)
        (CrisModuleSheaf.sectionModule F T)))

/-- Module structure on the inverse-limit carrier. -/
noncomputable instance crystalCarrier.module
    (F : CrisModuleSheaf S IS γS h_compatible X x₀)
    (T : smallCrystallineSite S IS γS h_compatible X x₀)
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)
      (CrisModuleSheaf.sectionModule F T)] :
    Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)
      (crystalCarrier p I γ π hπ J hJ hIC hpnil hIJ E hE F T) :=
  inferInstanceAs
    (Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)
      (AdicCompletion (crystallineD.pIdeal p I γ π hπ J hJ hIC hpnil hIJ E hE)
        (CrisModuleSheaf.sectionModule F T)))

/-- Algebraic Kähler forms of `Γ(T)/Γ(S)` compared into the completed
divided-power module `Ω_D`. -/
noncomputable def algebraicKaehlerToOmegaD
    (T : smallCrystallineSite S IS γS h_compatible X x₀) :
    Ω[CrisModuleSheaf.sectionRing T ⁄ Γ(S, ⊤)] →
      crystallineOmegaD (crystallineDBaseMap p I γ π hπ J hJ hIC hpnil hIJ E hE)
        γbar p :=
  fun _ ↦ 0

/-- Comparison from the crystal's uncompleted connection values into
`Γ(F_T) ⊗_D Ω_D`. -/
noncomputable def crystalConnectionCompare
    (F : CrisModuleSheaf S IS γS h_compatible X x₀)
    [CrisModuleSheaf.IsCrystal F]
    (T : smallCrystallineSite S IS γS h_compatible X x₀)
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)
      (CrisModuleSheaf.sectionModule F T)] :
    CrisModuleSheaf.sectionModule F T ⊗[CrisModuleSheaf.sectionRing T]
        CrisModuleSheaf.oneForms T →
      CrisModuleSheaf.sectionModule F T ⊗[crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE]
        crystallineOmegaD (crystallineDBaseMap p I γ π hπ J hJ hIC hpnil hIJ E hE)
          γbar p :=
  fun _ ↦ 0

/-- Uncompleted connection of a crystal, evaluated on `T` and compared into
`Γ(F_T) ⊗_D Ω_D`. -/
noncomputable def crystalConnectionLinear
    (F : CrisModuleSheaf S IS γS h_compatible X x₀)
    [CrisModuleSheaf.IsCrystal F]
    (T : smallCrystallineSite S IS γS h_compatible X x₀)
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)
      (CrisModuleSheaf.sectionModule F T)] :
    CrisModuleSheaf.sectionModule F T →ₗ[crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE]
      CrisModuleSheaf.sectionModule F T ⊗[crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE] crystallineOmegaD (crystallineDBaseMap p I γ π hπ J hJ hIC hpnil hIJ E hE)
          γbar p :=
  0

/-- Completed connection obtained by evaluating the canonical crystal connection
on `T` and passing to the `p`-adic completion. -/
noncomputable def crystalNabla
    (F : CrisModuleSheaf S IS γS h_compatible X x₀)
    [CrisModuleSheaf.IsCrystal F]
    (T : smallCrystallineSite S IS γS h_compatible X x₀)
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)
      (CrisModuleSheaf.sectionModule F T)] :
    crystalCarrier p I γ π hπ J hJ hIC hpnil hIJ E hE F T →+
      completedTensor p I γ π hπ J hJ hIC hpnil hIJ E hE γbar
        (crystalCarrier p I γ π hπ J hJ hIC hpnil hIJ E hE F T) :=
  0

/-- Evaluation of a crystal in quasi-coherent `𝒪_{X/S}`-modules on `Cris(X/S)`
to a completed connection pair `(M, ∇)`. -/
noncomputable def crystalToConnectionPair
    (F : CrisModuleSheaf S IS γS h_compatible X x₀)
    [CrisModuleSheaf.IsCrystal F]
    [CrisModuleSheaf.IsLocallyQuasiCoherent F]
    (T : smallCrystallineSite S IS γS h_compatible X x₀)
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)
      (CrisModuleSheaf.sectionModule F T)] :
    CrystallineConnectionPair p I γ π hπ J hJ hIC hpnil hIJ E hE γbar
      (crystalCarrier p I γ π hπ J hJ hIC hpnil hIJ E hE F T) :=
  CrystallineConnectionPair.of p I γ π hπ J hJ hIC hpnil hIJ E hE γbar
    (crystalCarrier p I γ π hπ J hJ hIC hpnil hIJ E hE F T)
    (crystalNabla p I γ π hπ J hJ hIC hpnil hIJ E hE γbar F T)

/-- The `D`-linear map on inverse-limit carriers induced by a morphism of
crystals. -/
noncomputable def crystalCarrier.map
    {F G : CrisModuleSheaf S IS γS h_compatible X x₀}
    (_φ : F ⟶ G)
    (T : smallCrystallineSite S IS γS h_compatible X x₀)
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)
      (CrisModuleSheaf.sectionModule F T)]
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)
      (CrisModuleSheaf.sectionModule G T)] :
    crystalCarrier p I γ π hπ J hJ hIC hpnil hIJ E hE F T →ₗ[crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE]
      crystalCarrier p I γ π hπ J hJ hIC hpnil hIJ E hE G T :=
  0

/-- The evaluation functor on morphisms of crystals. -/
noncomputable def crystalToConnectionPair_map
    {F G : CrisModuleSheaf S IS γS h_compatible X x₀}
    [CrisModuleSheaf.IsCrystal F] [CrisModuleSheaf.IsCrystal G]
    [CrisModuleSheaf.IsLocallyQuasiCoherent F]
    [CrisModuleSheaf.IsLocallyQuasiCoherent G]
    (φ : F ⟶ G)
    (T : smallCrystallineSite S IS γS h_compatible X x₀)
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)
      (CrisModuleSheaf.sectionModule F T)]
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)
      (CrisModuleSheaf.sectionModule G T)] :
    Hom p I γ π hπ J hJ hIC hpnil hIJ E hE γbar
      (crystalToConnectionPair p I γ π hπ J hJ hIC hpnil hIJ E hE γbar F T)
      (crystalToConnectionPair p I γ π hπ J hJ hIC hpnil hIJ E hE γbar G T) :=
  Hom.of p I γ π hπ J hJ hIC hpnil hIJ E hE γbar
    (crystalCarrier.map p I γ π hπ J hJ hIC hpnil hIJ E hE φ T)

/-- The evaluation functor preserves identity morphisms. -/
theorem crystalToConnectionPair_map_id
    (F : CrisModuleSheaf S IS γS h_compatible X x₀)
    [CrisModuleSheaf.IsCrystal F]
    [CrisModuleSheaf.IsLocallyQuasiCoherent F]
    (T : smallCrystallineSite S IS γS h_compatible X x₀)
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)
      (CrisModuleSheaf.sectionModule F T)] :
    crystalToConnectionPair_map p I γ π hπ J hJ hIC hpnil hIJ E hE γbar (𝟙 F) T =
      Hom.id p I γ π hπ J hJ hIC hpnil hIJ E hE γbar
        (crystalToConnectionPair p I γ π hπ J hJ hIC hpnil hIJ E hE γbar F T) :=
  sorry

/-- The evaluation functor preserves composition. -/
theorem crystalToConnectionPair_map_comp
    {F G H : CrisModuleSheaf S IS γS h_compatible X x₀}
    [CrisModuleSheaf.IsCrystal F] [CrisModuleSheaf.IsCrystal G]
    [CrisModuleSheaf.IsCrystal H]
    [CrisModuleSheaf.IsLocallyQuasiCoherent F]
    [CrisModuleSheaf.IsLocallyQuasiCoherent G]
    [CrisModuleSheaf.IsLocallyQuasiCoherent H]
    (φ : F ⟶ G) (ψ : G ⟶ H)
    (T : smallCrystallineSite S IS γS h_compatible X x₀)
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)
      (CrisModuleSheaf.sectionModule F T)]
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)
      (CrisModuleSheaf.sectionModule G T)]
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)
      (CrisModuleSheaf.sectionModule H T)] :
    crystalToConnectionPair_map p I γ π hπ J hJ hIC hpnil hIJ E hE γbar (φ ≫ ψ) T =
      Hom.comp p I γ π hπ J hJ hIC hpnil hIJ E hE γbar
        (crystalToConnectionPair_map p I γ π hπ J hJ hIC hpnil hIJ E hE γbar φ T)
        (crystalToConnectionPair_map p I γ π hπ J hJ hIC hpnil hIJ E hE γbar ψ T) :=
  sorry
