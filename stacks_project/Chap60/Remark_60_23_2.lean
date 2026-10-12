/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap60.Remark_60_23_2_Underlined
public import stacks_project.Chap60.Proposition_60_23_1
public import stacks_project.Chap60.Proposition_60_21_1
public import stacks_project.Chap60.Lemma_60_21_2_OmegaTensor
public import stacks_project.Chap60.Lemma_60_15_1
import Mathlib.Tactic.CrossRefAttribute
import StacksCheckRecall

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline
open CrystallineModuleSheaf

universe u

/-- The unit `𝒪_X`-module is quasi-coherent. -/
instance schemeModules_unit_isQuasicoherent (X : Scheme.{u}) :
    (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
  sorry

variable {S : Scheme.{u}} {I : S.IdealSheafData}
variable {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
variable {h_compatible :
  ∀ (V : S.affineOpens) (f : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
      (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
variable {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}

/-- The underlined sheaf of a quasi-coherent `𝒪_X`-module satisfies the
closed-immersion comparison-epimorphism condition of Proposition 60.21.1. -/
theorem CrisModuleSheaf.underlined_comparison_epi_of_closedImmersion
    (M : X.Modules) [M.IsQuasicoherent] :
    comparison_epi_of_closedImmersion S I γ h_compatible X x₀
      (CrisModuleSheaf.underlined I γ h_compatible x₀ M) :=
  sorry

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {h_I_quasiCoherent : I.toModule.IsQuasicoherent}
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
variable (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)

/-- Exterior powers of `Ω_{X/S}` remain locally quasi-coherent on `Cris(X/S)`. -/
instance crystallineOmegaPower_isLocallyQuasiCoherent (i : ℕ) :
    ModuleSheaf.IsLocallyQuasiCoherent (crystallineOmegaPower Ω i) :=
  sorry

/-- Exterior powers of `Ω_{X/S}` satisfy the closed-immersion comparison-epimorphism
condition of Proposition 60.21.1. -/
theorem crystallineOmegaPower_comparison_epi_of_closedImmersion (i : ℕ) :
    comparison_epi_of_closedImmersion S I γ h_compatible X x₀
      (crystallineOmegaPower Ω i) :=
  sorry

/-- Remark 60.23.2 (1): In Situation 60.7.5, `Ru_{X/S,*}(F ⊗_{𝒪_{X/S}} Ω^i_{X/S})`
vanishes for every `i > 0` whenever the `𝒪_{X/S}`-module `F` is locally quasi-coherent
and satisfies the comparison-epimorphism condition of Proposition 60.21.1 along
closed immersions of thickenings. -/
@[stacks 07LN]
theorem derivedSmallCrystallinePushforward_tensorOmegaPower_isZero_of_closedImmersionEpi
    (F : CrisModuleSheaf S I γ h_compatible X x₀)
    [ModuleSheaf.IsLocallyQuasiCoherent F]
    (h_epi : comparison_epi_of_closedImmersion S I γ h_compatible X x₀ F)
    [HasWeakSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}]
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).op.HasPointwiseRightKanExtension P]
    [HasSheafify X.smallZariskiTopology AddCommGrpCat.{u}]
    [Abelian (Sheaf X.smallZariskiTopology AddCommGrpCat.{u})]
    [HasDerivedCategory
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u})]
    [HasDerivedCategory (Sheaf X.smallZariskiTopology AddCommGrpCat.{u})]
    [IsGrothendieckAbelian
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u})]
    {i : ℕ} (hi : 0 < i) :
    IsZero
      (derivedSmallCrystallinePushforward_obj I γ h_compatible s x₀ h_p
        (toAbelianSheaf p S I γ h_compatible s X x₀ h_p
          (crystallineTensorOmegaPower F Ω i))) :=
  sorry

/-- Remark 60.23.2 (2): The vanishing of Remark 60.23.2 (1) applies to the sheaves
`Ω^j_{X/S}` for every `j`, which need not be crystals. -/
@[stacks 07LN]
theorem derivedSmallCrystallinePushforward_tensorOmegaPower_isZero_omegaPower
    [HasWeakSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}]
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).op.HasPointwiseRightKanExtension P]
    [HasSheafify X.smallZariskiTopology AddCommGrpCat.{u}]
    [Abelian (Sheaf X.smallZariskiTopology AddCommGrpCat.{u})]
    [HasDerivedCategory
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u})]
    [HasDerivedCategory (Sheaf X.smallZariskiTopology AddCommGrpCat.{u})]
    [IsGrothendieckAbelian
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u})]
    (j : ℕ) {i : ℕ} (hi : 0 < i) :
    IsZero
      (derivedSmallCrystallinePushforward_obj I γ h_compatible s x₀ h_p
        (toAbelianSheaf p S I γ h_compatible s X x₀ h_p
          (crystallineTensorOmegaPower (crystallineOmegaPower Ω j) Ω i))) :=
  sorry

/-- Remark 60.23.2 (3): The vanishing of Remark 60.23.2 (1) applies to
`CrisModuleSheaf.underlined` of any quasi-coherent `𝒪_X`-module. -/
@[stacks 07LN]
theorem derivedSmallCrystallinePushforward_tensorOmegaPower_isZero_underlined
    [HasWeakSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}]
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).op.HasPointwiseRightKanExtension P]
    [HasSheafify X.smallZariskiTopology AddCommGrpCat.{u}]
    [Abelian (Sheaf X.smallZariskiTopology AddCommGrpCat.{u})]
    [HasDerivedCategory
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u})]
    [HasDerivedCategory (Sheaf X.smallZariskiTopology AddCommGrpCat.{u})]
    [IsGrothendieckAbelian
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u})]
    (M : X.Modules) [M.IsQuasicoherent] {i : ℕ} (hi : 0 < i) :
    IsZero
      (derivedSmallCrystallinePushforward_obj I γ h_compatible s x₀ h_p
        (toAbelianSheaf p S I γ h_compatible s X x₀ h_p
          (crystallineTensorOmegaPower (CrisModuleSheaf.underlined I γ h_compatible x₀ M) Ω i))) :=
  sorry

/-- Remark 60.23.2 (4): In particular, the vanishing applies to
`CrisModuleSheaf.underlined` of the unit `𝒪_X`-module `SheafOfModules.unit`,
i.e. `underline 𝒪_X = underline G_a`. -/
@[stacks 07LN]
theorem derivedSmallCrystallinePushforward_tensorOmegaPower_isZero_underlined_unit
    [HasWeakSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}]
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).op.HasPointwiseRightKanExtension P]
    [HasSheafify X.smallZariskiTopology AddCommGrpCat.{u}]
    [Abelian (Sheaf X.smallZariskiTopology AddCommGrpCat.{u})]
    [HasDerivedCategory
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u})]
    [HasDerivedCategory (Sheaf X.smallZariskiTopology AddCommGrpCat.{u})]
    [IsGrothendieckAbelian
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u})]
    {i : ℕ} (hi : 0 < i) :
    IsZero
      (derivedSmallCrystallinePushforward_obj I γ h_compatible s x₀ h_p
        (toAbelianSheaf p S I γ h_compatible s X x₀ h_p
          (crystallineTensorOmegaPower
            (CrisModuleSheaf.underlined I γ h_compatible x₀
              (SheafOfModules.unit X.ringCatSheaf)) Ω i))) :=
  sorry

/- Remark 60.23.2 (5): a de Rham complex on `Cris(X/S)` requires the canonical integrable
connection of Lemma 60.15.1, which needs `F` to be a crystal. -/
@[stacks 07LN] #check canonicalConnection_isIntegrable

/- Remark 60.23.2 (6): currently the full statement of Proposition 60.23.1, including the
de Rham truncation isomorphism, is packaged on crystals in quasi-coherent modules. -/
@[stacks 07LN] #check derivedSmallCrystallinePushforward_deRhamTruncation_isIso

end
