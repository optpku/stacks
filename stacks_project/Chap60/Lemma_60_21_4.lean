/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap60.Proposition_60_21_3
public import stacks_project.Chap60.Lemma_60_17_5
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
variable {P' : Type u} [CommRing P'] [Algebra A P']
variable [Algebra.Smooth A P']
variable (π' : P' →ₐ[A] C)
variable (hπ' : Function.Surjective π')
variable (J' : Ideal P')
variable (hJ' : J' = RingHom.ker π'.toRingHom)
variable (hIJ' : Ideal.map (algebraMap A P') IA ≤ J')
variable (E' : DividedPowerEnvelope IA γA (algebraMap A P') J' hIJ')
variable (hE' : DividedPowerEnvelope.IsUniversal γA (algebraMap A P') hIJ' E')
variable (R : DividedPowerRetract p IA γA π' hπ' J' hJ' hIC hpnil hIJ' E' hE')
variable [HasLimits AddCommGrpCat.{u}]

/-- The `A`-module structure on `Ω_{D'}` is the one induced by completing the
relative divided-power differentials of the smooth envelope. -/
noncomputable instance module_crystallineOmegaDOf_overA :
    Module A
      (crystallineOmegaD
        (crystallineDOfBaseMap p IA γA π' hπ' J' hJ' hIC hpnil hIJ' E' hE') R.γbar' p) :=
  AdicCompletion.instModuleOfIsScalarTower
    (Ideal.span
      {(p : crystallineDOf p IA γA π' hπ' J' hJ' hIC hpnil hIJ' E' hE')})
    (dividedPowerDifferential
      (crystallineDOfBaseMap p IA γA π' hπ' J' hJ' hIC hpnil hIJ' E' hE') R.γbar')

/-- Scalar tower `A → D' → Ω_{D'}` for the completed relative differentials. -/
instance isScalarTower_crystallineOmegaDOf :
    IsScalarTower A R.smoothD
      (crystallineOmegaD
        (crystallineDOfBaseMap p IA γA π' hπ' J' hJ' hIC hpnil hIJ' E' hE') R.γbar' p) :=
  AdicCompletion.instIsScalarTower
    (Ideal.span
      {(p : crystallineDOf p IA γA π' hπ' J' hJ' hIC hpnil hIJ' E' hE')})
    (dividedPowerDifferential
      (crystallineDOfBaseMap p IA γA π' hπ' J' hJ' hIC hpnil hIJ' E' hE') R.γbar')

/-- Lemma 60.21.4: in the affine setup of Proposition 60.21.3, if `A → P' → C` is a
smooth presentation with kernel `J'` and `D'` is the p-adic completion of
`D_{P',γ}(J')`, then for a crystal `F` in quasi-coherent modules the completed
de Rham complex of the corresponding pair `(M', ∇')` over `D'` from Lemma 60.17.5
computes `RΓ(Cris(X/S), F)`. -/
@[stacks 07LH]
theorem affineCrystalSmoothCompletedDeRham_computes_derivedGlobalSections
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
    [Module R.polyD (CrisModuleSheaf.sectionModule F T)]
    (hComplete : IsAdicComplete
      (crystallineD.pIdeal p IA γA R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE)
      (crystalCarrier p IA γA R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE F T))
    (family : DifferentialOperator.DeRham.Family A R.smoothD R.omegaSmooth)
    (calculus :
      ExteriorCalculus
        (crystallineOmegaD_derivation
          (crystallineDOfBaseMap p IA γA π' hπ' J' hJ' hIC hpnil hIJ' E' hE') R.γbar' p)
        family)
    (conn :
      Connection
        (crystallineOmegaD_derivation
          (crystallineDOfBaseMap p IA γA π' hπ' J' hJ' hIC hpnil hIJ' E' hE') R.γbar' p)
        (baseChangeCarrierA p IA γA π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
          (crystalCarrier p IA γA R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE F T)))
    (h_corr : ∀ m,
      completedTensorOf.of p IA γA π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
          (baseChangeCarrierA p IA γA π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
            (crystalCarrier p IA γA R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE F T))
          (conn.toAddMonoidHom m) =
        baseChangeNablaAlongA p IA γA π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R hComplete
          (crystalToConnectionPair p IA γA R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE
            R.γbar F T).nabla m)
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
completed de Rham complex of the corresponding pair `(M', ∇')` over `D'`. -/
theorem affineCrystalSmoothCompletedDeRham_computes_cohomology
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
    [Module R.polyD (CrisModuleSheaf.sectionModule F T)]
    (hComplete : IsAdicComplete
      (crystallineD.pIdeal p IA γA R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE)
      (crystalCarrier p IA γA R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE F T))
    (family : DifferentialOperator.DeRham.Family A R.smoothD R.omegaSmooth)
    (calculus :
      ExteriorCalculus
        (crystallineOmegaD_derivation
          (crystallineDOfBaseMap p IA γA π' hπ' J' hJ' hIC hpnil hIJ' E' hE') R.γbar' p)
        family)
    (conn :
      Connection
        (crystallineOmegaD_derivation
          (crystallineDOfBaseMap p IA γA π' hπ' J' hJ' hIC hpnil hIJ' E' hE') R.γbar' p)
        (baseChangeCarrierA p IA γA π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
          (crystalCarrier p IA γA R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE F T)))
    (h_corr : ∀ m,
      completedTensorOf.of p IA γA π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
          (baseChangeCarrierA p IA γA π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
            (crystalCarrier p IA γA R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE F T))
          (conn.toAddMonoidHom m) =
        baseChangeNablaAlongA p IA γA π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R hComplete
          (crystalToConnectionPair p IA γA R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE
            R.γbar F T).nabla m)
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
