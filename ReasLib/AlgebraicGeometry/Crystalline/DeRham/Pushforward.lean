/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Embedding.Basic
public import ReasLib.AlgebraicGeometry.Crystalline.Pushforward.Abelian
public import ReasLib.AlgebraicGeometry.Crystalline.DeRham
public import ReasLib.AlgebraicGeometry.Crystalline.Base

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CrystallineModuleSheaf

universe u

namespace AlgebraicGeometry.Scheme.Crystalline

section

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {S : Scheme.{u}} {I : S.IdealSheafData}
variable {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
variable {h_compatible :
  ∀ (V : S.affineOpens) (f : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
      (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
variable (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
variable (F : CrisModuleSheaf S I γ h_compatible X x₀)
variable [CrisModuleSheaf.IsCrystal F]

/-- The derived crystalline direct image of the canonical de Rham truncation onto
the degree-zero coefficient, after extending from natural to integer degrees. -/
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

end

variable {p : ℕ} [Fact (Nat.Prime p)]
variable (B : Base.{u} p)
variable (F : CrisModuleSheaf B.scheme B.ideal B.dividedPowers B.compatible
  B.source B.sourceToClosed)

/-- The canonical de Rham truncation of a locally quasi-coherent crystal becomes
an isomorphism under derived crystalline direct image. -/
theorem derivedSmallCrystallinePushforward_deRhamTruncation_isIso
    [CrisModuleSheaf.IsCrystal F] [CrisModuleSheaf.IsLocallyQuasiCoherent F]
    [HasWeakSheafify
      (smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible
        B.toSpec B.source B.sourceToClosed B.prime_nilpotent) AddCommGrpCat.{u}]
    [HasSheafify
      (smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible
        B.toSpec B.source B.sourceToClosed B.prime_nilpotent) AddCommGrpCat.{u}]
    [∀ P : (smallCrystallineSite B.scheme B.ideal B.dividedPowers B.compatible
        B.source B.sourceToClosed)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (forgetfulFunctor p B.scheme B.ideal B.dividedPowers B.compatible
        B.toSpec B.source B.sourceToClosed B.prime_nilpotent).op.HasPointwiseRightKanExtension P]
    [HasSheafify B.source.smallZariskiTopology AddCommGrpCat.{u}]
    [Abelian (Sheaf B.source.smallZariskiTopology AddCommGrpCat.{u})]
    [HasDerivedCategory
      (Sheaf (smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible
        B.toSpec B.source B.sourceToClosed B.prime_nilpotent) AddCommGrpCat.{u})]
    [HasDerivedCategory (Sheaf B.source.smallZariskiTopology AddCommGrpCat.{u})]
    [IsGrothendieckAbelian
      (Sheaf (smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible
        B.toSpec B.source B.sourceToClosed B.prime_nilpotent) AddCommGrpCat.{u})]
    [HasZeroObject
      (Sheaf (smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible
        B.toSpec B.source B.sourceToClosed B.prime_nilpotent) AddCommGrpCat.{u})] :
    IsIso (derivedSmallCrystallinePushforward_deRhamTruncation B.toSpec B.prime_nilpotent F) := sorry

/-- Every positive differential-form tensor of a locally quasi-coherent crystal
has zero derived crystalline direct image. -/
theorem derivedSmallCrystallinePushforward_tensorOmegaPower_isZero
    [CrisModuleSheaf.IsCrystal F] [CrisModuleSheaf.IsLocallyQuasiCoherent F]
    (Ω : CrystallineDifferentials p B.scheme B.ideal B.dividedPowers B.compatible
      B.quasiCoherent B.toSpec B.source B.sourceToClosed B.prime_nilpotent)
    [HasWeakSheafify
      (smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible
        B.toSpec B.source B.sourceToClosed B.prime_nilpotent) AddCommGrpCat.{u}]
    [HasSheafify
      (smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible
        B.toSpec B.source B.sourceToClosed B.prime_nilpotent) AddCommGrpCat.{u}]
    [∀ P : (smallCrystallineSite B.scheme B.ideal B.dividedPowers B.compatible
        B.source B.sourceToClosed)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (forgetfulFunctor p B.scheme B.ideal B.dividedPowers B.compatible
        B.toSpec B.source B.sourceToClosed B.prime_nilpotent).op.HasPointwiseRightKanExtension P]
    [HasSheafify B.source.smallZariskiTopology AddCommGrpCat.{u}]
    [Abelian (Sheaf B.source.smallZariskiTopology AddCommGrpCat.{u})]
    [HasDerivedCategory
      (Sheaf (smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible
        B.toSpec B.source B.sourceToClosed B.prime_nilpotent) AddCommGrpCat.{u})]
    [HasDerivedCategory (Sheaf B.source.smallZariskiTopology AddCommGrpCat.{u})]
    [IsGrothendieckAbelian
      (Sheaf (smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible
        B.toSpec B.source B.sourceToClosed B.prime_nilpotent) AddCommGrpCat.{u})]
    {i : ℕ} (hi : 0 < i) :
    IsZero
      (derivedSmallCrystallinePushforward_obj B.ideal B.dividedPowers B.compatible
        B.toSpec B.sourceToClosed B.prime_nilpotent
        (toAbelianSheaf p B.scheme B.ideal B.dividedPowers B.compatible
          B.toSpec B.source B.sourceToClosed B.prime_nilpotent
          (crystallineTensorOmegaPower F Ω i))) := sorry

end AlgebraicGeometry.Scheme.Crystalline
