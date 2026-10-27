/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Pushforward.Abelian
public import ReasLib.AlgebraicGeometry.Crystalline.Base
public import ReasLib.AlgebraicGeometry.Crystalline.Module.Underlined.Conditions
public import ReasLib.AlgebraicGeometry.Crystalline.Module.Tensor.Conditions
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline CrystallineModuleSheaf

universe u

namespace AlgebraicGeometry.Scheme.Crystalline.DerivedPushforward

variable {p : ℕ} [Fact (Nat.Prime p)]
variable (B : Base.{u} p)
variable (Ω : CrystallineDifferentials p B.scheme B.ideal B.dividedPowers B.compatible
  B.quasiCoherent B.toSpec B.source B.sourceToClosed B.prime_nilpotent)

/-- A positive differential-form tensor of a locally quasi-coherent crystalline
module sheaf with epimorphic closed-immersion comparisons has zero derived direct image. -/
theorem tensorOmegaPower_isZero
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
    (F : CrisModuleSheaf B.scheme B.ideal B.dividedPowers B.compatible
      B.source B.sourceToClosed)
    (hqc : ModuleSheaf.IsLocallyQuasiCoherent F)
    (hF : IsCrisSheaf p B.toSpec B.prime_nilpotent F)
    (h_epi : comparison_epi_of_closedImmersion B.scheme B.ideal B.dividedPowers
      B.compatible B.source B.sourceToClosed F)
    {i : ℕ} (hi : 0 < i) :
    IsZero
      (derivedSmallCrystallinePushforward_obj B.ideal B.dividedPowers B.compatible
        B.toSpec B.sourceToClosed B.prime_nilpotent
        (toAbelianSheaf p B.scheme B.ideal B.dividedPowers B.compatible
          B.toSpec B.source B.sourceToClosed B.prime_nilpotent
          (crystallineTensorOmegaPower F Ω i))) := sorry

/-- The tensor of any crystalline differential power with a positive
differential power has zero derived crystalline direct image. -/
theorem tensorOmegaPower_isZero_omegaPower
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
    (j : ℕ) {i : ℕ} (hi : 0 < i) :
    IsZero
      (derivedSmallCrystallinePushforward_obj B.ideal B.dividedPowers B.compatible
        B.toSpec B.sourceToClosed B.prime_nilpotent
        (toAbelianSheaf p B.scheme B.ideal B.dividedPowers B.compatible
          B.toSpec B.source B.sourceToClosed B.prime_nilpotent
          (crystallineTensorOmegaPower (crystallineOmegaPower Ω j) Ω i))) := sorry

/-- A positive differential-form tensor of the underlined module of a
quasi-coherent source module has zero derived crystalline direct image. -/
theorem tensorOmegaPower_isZero_underlined
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
    (M : B.source.Modules) [M.IsQuasicoherent]
    {i : ℕ} (hi : 0 < i) :
    IsZero
      (derivedSmallCrystallinePushforward_obj B.ideal B.dividedPowers B.compatible
        B.toSpec B.sourceToClosed B.prime_nilpotent
        (toAbelianSheaf p B.scheme B.ideal B.dividedPowers B.compatible
          B.toSpec B.source B.sourceToClosed B.prime_nilpotent
          (crystallineTensorOmegaPower
            (CrisModuleSheaf.underlined B.ideal B.dividedPowers B.compatible
              B.sourceToClosed M) Ω i))) := sorry

/-- A positive differential-form tensor of the underlined structure module
has zero derived crystalline direct image. -/
theorem tensorOmegaPower_isZero_underlined_unit
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
          (crystallineTensorOmegaPower
            (CrisModuleSheaf.underlined B.ideal B.dividedPowers B.compatible
              B.sourceToClosed (SheafOfModules.unit B.source.ringCatSheaf)) Ω i))) := sorry

end AlgebraicGeometry.Scheme.Crystalline.DerivedPushforward
