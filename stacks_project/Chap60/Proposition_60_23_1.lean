/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Crystalline.DeRham.Pushforward

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline CrystallineModuleSheaf

universe u

/- Proposition 60.23.1 (1): The canonical de Rham truncation becomes an isomorphism
under derived crystalline direct image. -/
@[stacks 07LM] #check (AlgebraicGeometry.Scheme.Crystalline.derivedSmallCrystallinePushforward_deRhamTruncation_isIso :
    ∀ {p : ℕ} [Fact (Nat.Prime p)]
      (B : Base.{u} p)
      (F : CrisModuleSheaf B.scheme B.ideal B.dividedPowers B.compatible
        B.source B.sourceToClosed)
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
        B.toSpec B.source B.sourceToClosed B.prime_nilpotent) AddCommGrpCat.{u})],
    IsIso (derivedSmallCrystallinePushforward_deRhamTruncation B.toSpec B.prime_nilpotent F))

/- Proposition 60.23.1 (2): Positive differential-form tensors have zero derived
crystalline direct image. -/
@[stacks 07LM] #check (AlgebraicGeometry.Scheme.Crystalline.derivedSmallCrystallinePushforward_tensorOmegaPower_isZero :
    ∀ {p : ℕ} [Fact (Nat.Prime p)]
      (B : Base.{u} p)
      (F : CrisModuleSheaf B.scheme B.ideal B.dividedPowers B.compatible
        B.source B.sourceToClosed)
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
    {i : ℕ} (hi : 0 < i),
    IsZero
      (derivedSmallCrystallinePushforward_obj B.ideal B.dividedPowers B.compatible
        B.toSpec B.sourceToClosed B.prime_nilpotent
        (toAbelianSheaf p B.scheme B.ideal B.dividedPowers B.compatible
          B.toSpec B.source B.sourceToClosed B.prime_nilpotent
          (crystallineTensorOmegaPower F Ω i))))
