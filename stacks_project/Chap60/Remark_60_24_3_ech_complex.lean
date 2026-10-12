/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap60.Remark_60_24_3_ech_complex_Cover
public import stacks_project.Chap60.Remark_60_24_3_ech_complex_Envelope
public import stacks_project.Chap60.Remark_60_24_3_ech_complex_Geometric
public import stacks_project.Chap60.Remark_60_24_3_ech_complex_Eval
public import Mathlib.Algebra.Homology.Embedding.Basic
public import stacks_project.Chap60.Remark_60_24_3_ech_complex_Cosimplicial
public import stacks_project.Chap60.Lemma_60_18_2
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Crystalline
open AlgebraicGeometry.Scheme.Modules
open CrystallineModuleSheaf
open CechCrisCover
open CechCrisEnvelope

universe u

variable (p : ℕ) [Fact (Nat.Prime p)]
variable {A : Type u} [CommRing A]
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable (IA : Ideal A) (γA : DividedPowers IA)
variable {I : (Spec.{u} (.of A)).IdealSheafData}
variable {γS : ∀ V : (Spec.{u} (.of A)).affineOpens, DividedPowers (I.ideal V)}
variable {h_compatible :
    ∀ (V : (Spec.{u} (.of A)).affineOpens) (f : Γ(Spec (.of A), V)),
      (γS V).IsDPMorphism (γS ((Spec (.of A)).affineBasicOpen f))
        ((Spec (.of A)).presheaf.map
          (homOfLE ((Spec (.of A)).basicOpen_le f)).op).hom}
variable {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
variable (c : CechCrisCover x₀)
variable (s : Spec.{u} (.of A) ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
variable (E : CechCrisEnvelope p IA γA c)
variable [HasLimits AddCommGrpCat.{u}]

/-- Remark 60.24.3 (Čech complex) (1): for a prime `p`, a divided-power ring
`(A, I, γ)` with `A` a `ℤ_(p)`-algebra, `S = Spec A`, `S₀ = Spec(A / I)`, a
scheme `X` separated over `S₀` on which `p` is locally nilpotent, and a crystal
`F` in quasi-coherent `𝒪_{X/S}`-modules, an affine open covering
`U_idx = Spec C_idx` with polynomial presentations `P_idx → C_idx` determines a
cosimplicial completed PD envelope `D(*)` and a cosimplicial module `M(*)`,
and the associated cochain complex `s(M(*))` computes `RΓ(Cris(X/S), F)`. -/
@[stacks 07MM]
theorem cechCrisComplex_computes_derivedGlobalSections
    (hI : specIdealEqOfIdealTop IA I)
    (hγ : specDividedPowersEq IA γA I γS)
    [HasSheafify
      (smallCrystallineTopology p (Spec (.of A)) I γS h_compatible s X x₀ h_p)
      AddCommGrpCat.{u}]
    [HasSheafify (chaoticTopology (Spec (.of A)) I γS h_compatible X x₀)
      AddCommGrpCat.{u}]
    [HasTerminal (smallCrystallineSite (Spec (.of A)) I γS h_compatible X x₀)]
    [HasTerminal (chaoticSite (Spec (.of A)) I γS h_compatible X x₀)]
    [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
      (Sheaf (smallCrystallineTopology p (Spec (.of A)) I γS h_compatible s
        X x₀ h_p) AddCommGrpCat.{u})]
    [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
      (Sheaf (chaoticTopology (Spec (.of A)) I γS h_compatible X x₀)
        AddCommGrpCat.{u})]
    [HasExt (Sheaf (smallCrystallineTopology p (Spec (.of A)) I γS h_compatible s
      X x₀ h_p) AddCommGrpCat.{u})]
    (F : CrisModuleSheaf (Spec (.of A)) I γS h_compatible X x₀)
    [ModuleSheaf.IsLocallyQuasiCoherent F]
    [CrisModuleSheaf.IsCrystal F] :
    IsIsomorphic
      ((siteAbelianSectionsDerived
          (smallCrystallineTopology p (Spec (.of A)) I γS h_compatible s
            X x₀ h_p)
          (⊤_ (smallCrystallineSite (Spec (.of A)) I γS h_compatible X x₀))).obj
        ((DerivedCategory.singleFunctor
            (Sheaf (smallCrystallineTopology p (Spec (.of A)) I γS h_compatible s
              X x₀ h_p) AddCommGrpCat.{u}) 0).obj
          (toAbelianSheaf p (Spec (.of A)) I γS h_compatible s X x₀ h_p F)))
      ((DerivedCategory.Q).obj
        ((ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u}).obj
          ((E.cechCrisComplex) s h_p hI hγ F))) :=
  sorry

/-- Remark 60.24.3 (Čech complex) (2): the same derived-category comparison
`RΓ(Cris(X/S), F) ≅ Q(s(M(*)))` holds for any module satisfying the
quasi-coherence and closed-immersion hypotheses of Proposition 60.21.1,
without requiring `F` to be a crystal. -/
@[stacks 07MM]
theorem cechCrisComplex_computes_derivedGlobalSections_of_locallyQuasiCoherent
    (hI : specIdealEqOfIdealTop IA I)
    (hγ : specDividedPowersEq IA γA I γS)
    [HasSheafify
      (smallCrystallineTopology p (Spec (.of A)) I γS h_compatible s X x₀ h_p)
      AddCommGrpCat.{u}]
    [HasSheafify (chaoticTopology (Spec (.of A)) I γS h_compatible X x₀)
      AddCommGrpCat.{u}]
    [HasTerminal (smallCrystallineSite (Spec (.of A)) I γS h_compatible X x₀)]
    [HasTerminal (chaoticSite (Spec (.of A)) I γS h_compatible X x₀)]
    [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
      (Sheaf (smallCrystallineTopology p (Spec (.of A)) I γS h_compatible s
        X x₀ h_p) AddCommGrpCat.{u})]
    [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
      (Sheaf (chaoticTopology (Spec (.of A)) I γS h_compatible X x₀)
        AddCommGrpCat.{u})]
    [HasExt (Sheaf (smallCrystallineTopology p (Spec (.of A)) I γS h_compatible s
      X x₀ h_p) AddCommGrpCat.{u})]
    (F : CrisModuleSheaf (Spec (.of A)) I γS h_compatible X x₀)
    [ModuleSheaf.IsLocallyQuasiCoherent F]
    (h_epi : comparison_epi_of_closedImmersion (Spec (.of A)) I γS h_compatible
      X x₀ F) :
    IsIsomorphic
      ((siteAbelianSectionsDerived
          (smallCrystallineTopology p (Spec (.of A)) I γS h_compatible s
            X x₀ h_p)
          (⊤_ (smallCrystallineSite (Spec (.of A)) I γS h_compatible X x₀))).obj
        ((DerivedCategory.singleFunctor
            (Sheaf (smallCrystallineTopology p (Spec (.of A)) I γS h_compatible s
              X x₀ h_p) AddCommGrpCat.{u}) 0).obj
          (toAbelianSheaf p (Spec (.of A)) I γS h_compatible s X x₀ h_p F)))
      ((DerivedCategory.Q).obj
        ((ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u}).obj
          ((E.cechCrisComplex) s h_p hI hγ F))) :=
  sorry

end
