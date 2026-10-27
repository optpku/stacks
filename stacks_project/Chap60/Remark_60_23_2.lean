/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Pushforward.Vanishing
public import ReasLib.AlgebraicGeometry.Crystalline.Connection
public import ReasLib.AlgebraicGeometry.Crystalline.DeRham.Pushforward
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline CrystallineModuleSheaf

universe u

variable {p : ℕ} [Fact (Nat.Prime p)]
variable (B : Base.{u} p)
variable (Ω : CrystallineDifferentials p B.scheme B.ideal B.dividedPowers B.compatible
  B.quasiCoherent B.toSpec B.source B.sourceToClosed B.prime_nilpotent)

variable
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

/- Remark 60.23.2 (1): Locally quasi-coherent crystalline module sheaves with
epimorphic closed-immersion comparisons have positive-form tensor vanishing;
no crystal condition is required. -/
@[stacks 07LN] #check
  (AlgebraicGeometry.Scheme.Crystalline.DerivedPushforward.tensorOmegaPower_isZero B Ω :
    ∀ (F : CrisModuleSheaf B.scheme B.ideal B.dividedPowers B.compatible
      B.source B.sourceToClosed)
    (hqc : ModuleSheaf.IsLocallyQuasiCoherent F)
    (hF : IsCrisSheaf p B.toSpec B.prime_nilpotent F)
    (h_epi : comparison_epi_of_closedImmersion B.scheme B.ideal B.dividedPowers
      B.compatible B.source B.sourceToClosed F)
    {i : ℕ} (hi : 0 < i),
    IsZero
      (derivedSmallCrystallinePushforward_obj B.ideal B.dividedPowers B.compatible
        B.toSpec B.sourceToClosed B.prime_nilpotent
        (toAbelianSheaf p B.scheme B.ideal B.dividedPowers B.compatible
          B.toSpec B.source B.sourceToClosed B.prime_nilpotent
          (crystallineTensorOmegaPower F Ω i))))

/- Remark 60.23.2 (2): This vanishing applies to every differential power,
including degree zero, without a crystal condition. -/
@[stacks 07LN] #check
  (AlgebraicGeometry.Scheme.Crystalline.DerivedPushforward.tensorOmegaPower_isZero_omegaPower B Ω :
    ∀ (j : ℕ) {i : ℕ} (hi : 0 < i),
    IsZero
      (derivedSmallCrystallinePushforward_obj B.ideal B.dividedPowers B.compatible
        B.toSpec B.sourceToClosed B.prime_nilpotent
        (toAbelianSheaf p B.scheme B.ideal B.dividedPowers B.compatible
          B.toSpec B.source B.sourceToClosed B.prime_nilpotent
          (crystallineTensorOmegaPower (crystallineOmegaPower Ω j) Ω i))))

/- Remark 60.23.2 (3): This vanishing applies to the underlined module of
any quasi-coherent source module. -/
@[stacks 07LN] #check
  (AlgebraicGeometry.Scheme.Crystalline.DerivedPushforward.tensorOmegaPower_isZero_underlined B Ω :
    ∀ (M : B.source.Modules) [M.IsQuasicoherent]
    {i : ℕ} (hi : 0 < i),
    IsZero
      (derivedSmallCrystallinePushforward_obj B.ideal B.dividedPowers B.compatible
        B.toSpec B.sourceToClosed B.prime_nilpotent
        (toAbelianSheaf p B.scheme B.ideal B.dividedPowers B.compatible
          B.toSpec B.source B.sourceToClosed B.prime_nilpotent
          (crystallineTensorOmegaPower
            (CrisModuleSheaf.underlined B.ideal B.dividedPowers B.compatible
              B.sourceToClosed M) Ω i))))

/- Remark 60.23.2 (4): In particular it applies to the underlined structure
module, the additive structure sheaf. -/
@[stacks 07LN] #check
  (AlgebraicGeometry.Scheme.Crystalline.DerivedPushforward.tensorOmegaPower_isZero_underlined_unit B Ω :
    ∀ {i : ℕ} (hi : 0 < i),
    IsZero
      (derivedSmallCrystallinePushforward_obj B.ideal B.dividedPowers B.compatible
        B.toSpec B.sourceToClosed B.prime_nilpotent
        (toAbelianSheaf p B.scheme B.ideal B.dividedPowers B.compatible
          B.toSpec B.source B.sourceToClosed B.prime_nilpotent
          (crystallineTensorOmegaPower
            (CrisModuleSheaf.underlined B.ideal B.dividedPowers B.compatible
              B.sourceToClosed (SheafOfModules.unit B.source.ringCatSheaf)) Ω i))))

variable (F : CrisModuleSheaf B.scheme B.ideal B.dividedPowers B.compatible
  B.source B.sourceToClosed) [CrisModuleSheaf.IsCrystal F]
variable (T : smallCrystallineSite B.scheme B.ideal B.dividedPowers B.compatible
  B.source B.sourceToClosed)

/- Remark 60.23.2 (5): The canonical de Rham construction uses the integrable
connection supplied for crystals. This does not exclude other constructions
for particular non-crystals. -/
@[stacks 07LN] #check (canonicalConnection_isIntegrable F T :
    SheafOfModules.RingedSite.Connection.IsIntegrable.{u, u}
      (CrystallineModuleSheaf.CrisModuleSheaf.canonicalConnection F T)
      (CrystallineModuleSheaf.CrisModuleSheaf.exteriorCalculus T))

variable [CrisModuleSheaf.IsLocallyQuasiCoherent F]
variable [HasZeroObject
  (Sheaf (smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible
    B.toSpec B.source B.sourceToClosed B.prime_nilpotent) AddCommGrpCat.{u})]

/- Remark 60.23.2 (6): The current full de Rham truncation theorem applies to
crystals in quasi-coherent modules. -/
@[stacks 07LN] #check
  (AlgebraicGeometry.Scheme.Crystalline.derivedSmallCrystallinePushforward_deRhamTruncation_isIso B F :
    IsIso (AlgebraicGeometry.Scheme.Crystalline.derivedSmallCrystallinePushforward_deRhamTruncation
      B.toSpec B.prime_nilpotent F))
