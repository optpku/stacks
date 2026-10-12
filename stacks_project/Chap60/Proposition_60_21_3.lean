/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Embedding.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import stacks_project.Chap60.Proposition_60_21_1
public import stacks_project.Chap60.Proposition_60_17_4
public import stacks_project.Chap60.Lemma_60_17_3_Functor
public import stacks_project.Chap60.Lemma_60_20_2_Completion
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Crystalline
open AlgebraicGeometry.Scheme.Modules
open CompletedCris
open CrystallineModuleSheaf
open CrystallineConnectionPair
open DPPolynomial.DeRham

universe u

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {A : Type u} [CommRing A] {IA : Ideal A} (γA : DividedPowers IA)
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable {C : Type u} [CommRing C] [Algebra A C]
variable (hIC : Ideal.map (algebraMap A C) IA = (⊥ : Ideal C))
variable (hpnil : IsNilpotent (p : C))
variable {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C)
variable (hπ : Function.Surjective π)
variable (J0 : Ideal (MvPolynomial ι A))
variable (hJ0 : J0 = RingHom.ker π.toRingHom)
variable (hIJ0 : Ideal.map (algebraMap A (MvPolynomial ι A)) IA ≤ J0)
variable (E0 : DividedPowerEnvelope IA γA (algebraMap A (MvPolynomial ι A)) J0 hIJ0)
variable (hE0 : DividedPowerEnvelope.IsUniversal γA
  (algebraMap A (MvPolynomial ι A)) hIJ0 E0)
variable (γbar : DividedPowers
  (Ideal.map (algebraMap E0.D
    (crystallineD p IA γA π hπ J0 hJ0 hIC hpnil hIJ0 E0 hE0)) E0.D.ideal))
variable [HasLimits AddCommGrpCat.{u}]

/-- The `A`-module structure on `Ω_D` is the one induced by completing the
relative divided-power differentials. -/
noncomputable instance module_crystallineOmegaD_overA :
    Module A
      (crystallineOmegaD
        (crystallineDBaseMap p IA γA π hπ J0 hJ0 hIC hpnil hIJ0 E0 hE0) γbar p) :=
  AdicCompletion.instModuleOfIsScalarTower
    (Ideal.span
      {(p : crystallineD p IA γA π hπ J0 hJ0 hIC hpnil hIJ0 E0 hE0)})
    (dividedPowerDifferential
      (crystallineDBaseMap p IA γA π hπ J0 hJ0 hIC hpnil hIJ0 E0 hE0) γbar)

/-- Scalar tower `A → D → Ω_D` for the completed relative differentials. -/
instance isScalarTower_crystallineOmegaD :
    IsScalarTower A
      (crystallineD p IA γA π hπ J0 hJ0 hIC hpnil hIJ0 E0 hE0)
      (crystallineOmegaD
        (crystallineDBaseMap p IA γA π hπ J0 hJ0 hIC hpnil hIJ0 E0 hE0) γbar p) :=
  AdicCompletion.instIsScalarTower
    (Ideal.span
      {(p : crystallineD p IA γA π hπ J0 hJ0 hIC hpnil hIJ0 E0 hE0)})
    (dividedPowerDifferential
      (crystallineDBaseMap p IA γA π hπ J0 hJ0 hIC hpnil hIJ0 E0 hE0) γbar)

/-- Closed-immersion comparison maps of a crystal in quasi-coherent modules are
epimorphisms, so the comparison-epi hypothesis of Proposition 60.21.1 holds. -/
theorem comparison_epi_of_quasiCoherentCrystal
    (I : (Spec.{u} (.of A)).IdealSheafData)
    (γS : ∀ V : (Spec.{u} (.of A)).affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : (Spec.{u} (.of A)).affineOpens) (f : Γ(Spec (.of A), V)),
        (γS V).IsDPMorphism (γS ((Spec (.of A)).affineBasicOpen f))
          ((Spec (.of A)).presheaf.map
            (homOfLE ((Spec (.of A)).basicOpen_le f)).op).hom)
    (x₀ : Spec.{u} (.of C) ⟶ I.subscheme)
    (F : CrisModuleSheaf (Spec (.of A)) I γS h_compatible (Spec (.of C)) x₀)
    [IsQuasiCoherentCrystal F] :
    comparison_epi_of_closedImmersion (Spec (.of A)) I γS h_compatible
      (Spec (.of C)) x₀ F :=
  sorry

/-- Proposition 60.21.3: in the affine setup of Proposition 60.21.1, if `F` is a
crystal in quasi-coherent modules and `(M, ∇)` is the corresponding integrable
connection over `D` from Proposition 60.17.4, then the p-adically completed
de Rham complex `completedDeRhamComplex` of `M ⊗^∧_D Ω^*_D` computes
`RΓ(Cris(X/S), F)`. -/
@[stacks 07LG]
theorem affineCrystalCompletedDeRham_computes_derivedGlobalSections
    (I : (Spec.{u} (.of A)).IdealSheafData)
    (γS : ∀ V : (Spec.{u} (.of A)).affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : (Spec.{u} (.of A)).affineOpens) (f : Γ(Spec (.of A), V)),
        (γS V).IsDPMorphism (γS ((Spec (.of A)).affineBasicOpen f))
          ((Spec (.of A)).presheaf.map
            (homOfLE ((Spec (.of A)).basicOpen_le f)).op).hom)
    (s : Spec.{u} (.of A) ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (x₀ : Spec.{u} (.of C) ⟶ I.subscheme)
    (h_p : ∀ U : (Spec.{u} (.of C)).affineOpens,
      IsNilpotent (p : Γ(Spec (.of C), U)))
    (hI : specIdealEqOfIdealTop IA I)
    (hγ : specDividedPowersEq IA γA I γS)
    (hx₀ : IsCanonicalCrisStructureMap I x₀)
    [HasSheafify
      (smallCrystallineTopology p (Spec (.of A)) I γS h_compatible s
        (Spec (.of C)) x₀ h_p)
      AddCommGrpCat.{u}]
    [HasSheafify (chaoticTopology (Spec (.of A)) I γS h_compatible (Spec (.of C)) x₀)
      AddCommGrpCat.{u}]
    [HasTerminal (smallCrystallineSite (Spec (.of A)) I γS h_compatible
      (Spec (.of C)) x₀)]
    [HasTerminal (chaoticSite (Spec (.of A)) I γS h_compatible (Spec (.of C)) x₀)]
    [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
      (Sheaf (smallCrystallineTopology p (Spec (.of A)) I γS h_compatible s
        (Spec (.of C)) x₀ h_p) AddCommGrpCat.{u})]
    [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
      (Sheaf (chaoticTopology (Spec (.of A)) I γS h_compatible (Spec (.of C)) x₀)
        AddCommGrpCat.{u})]
    [HasSheafify (⊥ : GrothendieckTopology
      (crisOppSite γA (algebraMap A C) hIC hpnil)) AddCommGrpCat.{u}]
    [HasExt (Sheaf (smallCrystallineTopology p (Spec (.of A)) I γS h_compatible s
      (Spec (.of C)) x₀ h_p) AddCommGrpCat.{u})]
    (F : CrisModuleSheaf (Spec (.of A)) I γS h_compatible (Spec (.of C)) x₀)
    [IsQuasiCoherentCrystal F]
    (T : smallCrystallineSite (Spec (.of A)) I γS h_compatible (Spec (.of C)) x₀)
    [Module (crystallineD p IA γA π hπ J0 hJ0 hIC hpnil hIJ0 E0 hE0)
      (CrisModuleSheaf.sectionModule F T)]
    (family :
      DifferentialOperator.DeRham.Family A
        (crystallineD p IA γA π hπ J0 hJ0 hIC hpnil hIJ0 E0 hE0)
        (crystallineOmegaD
          (crystallineDBaseMap p IA γA π hπ J0 hJ0 hIC hpnil hIJ0 E0 hE0) γbar p))
    (calculus :
      ExteriorCalculus
        (crystallineOmegaD_derivation
          (crystallineDBaseMap p IA γA π hπ J0 hJ0 hIC hpnil hIJ0 E0 hE0) γbar p)
        family)
    (conn :
      Connection
        (crystallineOmegaD_derivation
          (crystallineDBaseMap p IA γA π hπ J0 hJ0 hIC hpnil hIJ0 E0 hE0) γbar p)
        (crystalCarrier p IA γA π hπ J0 hJ0 hIC hpnil hIJ0 E0 hE0 F T))
    (h_corr : ∀ m,
      completedTensor.of p IA γA π hπ J0 hJ0 hIC hpnil hIJ0 E0 hE0 γbar
          (crystalCarrier p IA γA π hπ J0 hJ0 hIC hpnil hIJ0 E0 hE0 F T)
          (conn.toAddMonoidHom m) =
        (crystalToConnectionPair p IA γA π hπ J0 hJ0 hIC hpnil hIJ0 E0 hE0 γbar
          F T).nabla m)
    (hconn : Connection.IsIntegrable conn calculus) :
    IsIsomorphic
      ((siteAbelianSectionsDerived
          (smallCrystallineTopology p (Spec (.of A)) I γS h_compatible s
            (Spec (.of C)) x₀ h_p)
          (⊤_ (smallCrystallineSite (Spec (.of A)) I γS h_compatible
            (Spec (.of C)) x₀))).obj
        ((DerivedCategory.singleFunctor
            (Sheaf (smallCrystallineTopology p (Spec (.of A)) I γS h_compatible s
              (Spec (.of C)) x₀ h_p) AddCommGrpCat.{u}) 0).obj
          (toAbelianSheaf p (Spec (.of A)) I γS h_compatible s (Spec (.of C)) x₀ h_p
            F)))
      ((DerivedCategory.Q).obj
        ((ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u}).obj
          (completedDeRhamComplex calculus hconn p))) :=
  sorry

/-- Degreewise cohomology of `RΓ(Cris(X/S), F)` agrees with homology of the
completed de Rham complex of the corresponding pair `(M, ∇)`. -/
theorem affineCrystalCompletedDeRham_computes_cohomology
    (I : (Spec.{u} (.of A)).IdealSheafData)
    (γS : ∀ V : (Spec.{u} (.of A)).affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : (Spec.{u} (.of A)).affineOpens) (f : Γ(Spec (.of A), V)),
        (γS V).IsDPMorphism (γS ((Spec (.of A)).affineBasicOpen f))
          ((Spec (.of A)).presheaf.map
            (homOfLE ((Spec (.of A)).basicOpen_le f)).op).hom)
    (s : Spec.{u} (.of A) ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (x₀ : Spec.{u} (.of C) ⟶ I.subscheme)
    (h_p : ∀ U : (Spec.{u} (.of C)).affineOpens,
      IsNilpotent (p : Γ(Spec (.of C), U)))
    (hI : specIdealEqOfIdealTop IA I)
    (hγ : specDividedPowersEq IA γA I γS)
    (hx₀ : IsCanonicalCrisStructureMap I x₀)
    [HasSheafify
      (smallCrystallineTopology p (Spec (.of A)) I γS h_compatible s
        (Spec (.of C)) x₀ h_p)
      AddCommGrpCat.{u}]
    [HasSheafify (chaoticTopology (Spec (.of A)) I γS h_compatible (Spec (.of C)) x₀)
      AddCommGrpCat.{u}]
    [HasTerminal (smallCrystallineSite (Spec (.of A)) I γS h_compatible
      (Spec (.of C)) x₀)]
    [HasTerminal (chaoticSite (Spec (.of A)) I γS h_compatible (Spec (.of C)) x₀)]
    [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
      (Sheaf (smallCrystallineTopology p (Spec (.of A)) I γS h_compatible s
        (Spec (.of C)) x₀ h_p) AddCommGrpCat.{u})]
    [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
      (Sheaf (chaoticTopology (Spec (.of A)) I γS h_compatible (Spec (.of C)) x₀)
        AddCommGrpCat.{u})]
    [HasSheafify (⊥ : GrothendieckTopology
      (crisOppSite γA (algebraMap A C) hIC hpnil)) AddCommGrpCat.{u}]
    [HasExt (Sheaf (smallCrystallineTopology p (Spec (.of A)) I γS h_compatible s
      (Spec (.of C)) x₀ h_p) AddCommGrpCat.{u})]
    (F : CrisModuleSheaf (Spec (.of A)) I γS h_compatible (Spec (.of C)) x₀)
    [IsQuasiCoherentCrystal F]
    (T : smallCrystallineSite (Spec (.of A)) I γS h_compatible (Spec (.of C)) x₀)
    [Module (crystallineD p IA γA π hπ J0 hJ0 hIC hpnil hIJ0 E0 hE0)
      (CrisModuleSheaf.sectionModule F T)]
    (family :
      DifferentialOperator.DeRham.Family A
        (crystallineD p IA γA π hπ J0 hJ0 hIC hpnil hIJ0 E0 hE0)
        (crystallineOmegaD
          (crystallineDBaseMap p IA γA π hπ J0 hJ0 hIC hpnil hIJ0 E0 hE0) γbar p))
    (calculus :
      ExteriorCalculus
        (crystallineOmegaD_derivation
          (crystallineDBaseMap p IA γA π hπ J0 hJ0 hIC hpnil hIJ0 E0 hE0) γbar p)
        family)
    (conn :
      Connection
        (crystallineOmegaD_derivation
          (crystallineDBaseMap p IA γA π hπ J0 hJ0 hIC hpnil hIJ0 E0 hE0) γbar p)
        (crystalCarrier p IA γA π hπ J0 hJ0 hIC hpnil hIJ0 E0 hE0 F T))
    (h_corr : ∀ m,
      completedTensor.of p IA γA π hπ J0 hJ0 hIC hpnil hIJ0 E0 hE0 γbar
          (crystalCarrier p IA γA π hπ J0 hJ0 hIC hpnil hIJ0 E0 hE0 F T)
          (conn.toAddMonoidHom m) =
        (crystalToConnectionPair p IA γA π hπ J0 hJ0 hIC hpnil hIJ0 E0 hE0 γbar
          F T).nabla m)
    (hconn : Connection.IsIntegrable conn calculus)
    (n : ℕ) :
    IsIsomorphic
      ((Sheaf.functorH
          (smallCrystallineTopology p (Spec (.of A)) I γS h_compatible s
            (Spec (.of C)) x₀ h_p) n).obj
        (toAbelianSheaf p (Spec (.of A)) I γS h_compatible s (Spec (.of C)) x₀ h_p F))
      ((completedDeRhamComplex calculus hconn p).homology n) :=
  sorry

end
