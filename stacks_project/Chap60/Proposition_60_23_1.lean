module

public import Mathlib.Algebra.Homology.Embedding.Basic
public import Mathlib.CategoryTheory.Sites.Abelian
public import stacks_project.Chap60.Lemma_60_21_2_OmegaTensor
public import stacks_project.Chap60.Proposition_60_23_1_DeRham
public import stacks_project.Chap60.Proposition_60_23_1_Pushforward
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline
open CrystallineModuleSheaf

universe u

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {S : Scheme.{u}} {I : S.IdealSheafData}
variable {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
variable {h_compatible :
  ∀ (V : S.affineOpens) (f : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
      (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
variable {h_I_quasiCoherent : I.toModule.IsQuasicoherent}
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
variable (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
variable (F : CrisModuleSheaf S I γ h_compatible X x₀)
variable [IsQuasiCoherentCrystal F]
variable (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)

/-- `Ru_{X/S,*}` of the stupid truncation of `crystalDeRhamComplex F` onto `F[0]`,
after extending the `ℕ`-indexed complex to `ℤ` and applying `DerivedCategory.Q`. -/
def derivedSmallCrystallinePushforward_deRhamTruncation
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
    [HasZeroObject
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u})] :=
  let Ru := derivedSmallCrystallinePushforward I γ h_compatible s x₀ h_p
  let extendZ :=
    ComplexShape.embeddingUpNat.extendFunctor
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u})
  Ru.map (DerivedCategory.Q.map (extendZ.map (crystalDeRhamTruncation p s h_p F)))

/-- Proposition 60.23.1 (1): In Situation 60.7.5, if `F` is a crystal in quasi-coherent
modules on `Cris(X/S)`, then the truncation of the crystalline de Rham complex
`crystalDeRhamComplex F` onto `F[0]` becomes an isomorphism after applying
`derivedSmallCrystallinePushforward` (`Ru_{X/S,*}`). The truncation itself need
not be a quasi-isomorphism. -/
@[stacks 07LM]
theorem derivedSmallCrystallinePushforward_deRhamTruncation_isIso
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
    [HasZeroObject
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u})] :
    IsIso (derivedSmallCrystallinePushforward_deRhamTruncation s h_p F) :=
  sorry

/-- Proposition 60.23.1 (2): In Situation 60.7.5, if `F` is a crystal in quasi-coherent
modules on `Cris(X/S)`, then `Ru_{X/S,*}(F ⊗_{𝒪_{X/S}} Ω^i_{X/S})` is zero in the
derived category of abelian sheaves on `X_Zariski` for every `i > 0`. -/
@[stacks 07LM]
theorem derivedSmallCrystallinePushforward_tensorOmegaPower_isZero
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
