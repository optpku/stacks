module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import stacks_project.Chap60.Proposition_60_21_1
public import stacks_project.Chap60.Lemma_60_21_2_OmegaTensor
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline
open CompletedCris
open CrystallineModuleSheaf

universe u

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {A : Type u} [CommRing A] {IA : Ideal A} (γA : DividedPowers IA)
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable {C : Type u} [CommRing C] [Algebra A C]
variable (hIC : Ideal.map (algebraMap A C) IA = (⊥ : Ideal C))
variable (hpnil : IsNilpotent (p : C))

include hIC hpnil in
/-- Lemma 60.21.2: under the affine Situation of Proposition 60.21.1, crystalline
cohomology `H^j(Cris(X/S), F ⊗_{𝒪_{X/S}} Ω^i_{X/S})` vanishes for every `i > 0`
and every `j : ℕ`. The hypotheses `hF` and `hΩ` supply the intrinsic sheaf
laws absent from the underlying module-assignment types. -/
@[stacks 07LF]
theorem affineCris_tensorOmegaPower_cohomology_isZero
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
    (h_I_quasiCoherent : I.toModule.IsQuasicoherent)
    [HasSheafify
      (smallCrystallineTopology p (Spec (.of A)) I γS h_compatible s
        (Spec (.of C)) x₀ h_p)
      AddCommGrpCat.{u}]
    [HasExt (Sheaf (smallCrystallineTopology p (Spec (.of A)) I γS h_compatible s
      (Spec (.of C)) x₀ h_p) AddCommGrpCat.{u})]
    (F : CrisModuleSheaf (Spec (.of A)) I γS h_compatible (Spec (.of C)) x₀)
    (hF : IsCrisSheaf p s h_p F)
    [ModuleSheaf.IsLocallyQuasiCoherent F]
    (h_epi : comparison_epi_of_closedImmersion (Spec (.of A)) I γS h_compatible
      (Spec (.of C)) x₀ F)
    (Ω : CrystallineDifferentials p (Spec (.of A)) I γS h_compatible
      h_I_quasiCoherent s (Spec (.of C)) x₀ h_p)
    (hΩ : IsCrisSheaf p s h_p (restrictCrystallineModule Ω.module))
    (i j : ℕ) (hi : 0 < i) :
    IsZero
      ((Sheaf.functorH
          (smallCrystallineTopology p (Spec (.of A)) I γS h_compatible s
            (Spec (.of C)) x₀ h_p) j).obj
        (crystallineTensorOmegaPowerSheaf p s h_p F hF Ω hΩ i)) := sorry

end
