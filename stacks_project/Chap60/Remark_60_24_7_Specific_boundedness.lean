/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Crystalline.Cohomology.Boundedness

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Crystalline SheafOfModules

universe u v

/- Remark 60.24.7 (Specific boundedness) (1): crystalline cohomology vanishes above the
sum of the source dimension and the relative embedding-dimension bound. -/
@[stacks 07MR] #check
  (AlgebraicGeometry.Scheme.Crystalline.isZero_of_dim_add_embeddingDimension :
    ∀ {p : ℕ} [Fact p.Prime] (B : Base.{u} p)
    [Unique B.ideal.subscheme] [FinitePresentation B.sourceToClosed]
    [HasSheafify
      (smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
        B.source B.sourceToClosed B.prime_nilpotent) AddCommGrpCat.{u}]
    [HasExt.{v} (Sheaf
      (smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
        B.source B.sourceToClosed B.prime_nilpotent) AddCommGrpCat.{u})]
    [∀ U : smallCrystallineSite B.scheme B.ideal B.dividedPowers B.compatible
        B.source B.sourceToClosed,
      HasWeakSheafify
        ((smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
          B.source B.sourceToClosed B.prime_nilpotent).over U) AddCommGrpCat.{u}]
    [∀ U : smallCrystallineSite B.scheme B.ideal B.dividedPowers B.compatible
        B.source B.sourceToClosed,
      ((smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
        B.source B.sourceToClosed B.prime_nilpotent).over U).WEqualsLocallyBijective
          AddCommGrpCat.{u}]
    (F : SheafOfModules.{u}
      (smallCrystallineStructureSheaf B.ideal B.dividedPowers B.compatible B.toSpec
        B.sourceToClosed B.prime_nilpotent))
    [IsCrystalInQuasiCoherentModules F]
    (d e i : ℕ) (h_dim : topologicalKrullDim B.source = (d : WithBot ℕ∞))
    (h_emb : B.sourceToClosed.HasEmbeddingDimensionLE e) (hi : d + e < i),
    IsZero
      ((Sheaf.functorH
        (smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
          B.source B.sourceToClosed B.prime_nilpotent) i).obj
        ((SheafOfModules.toSheaf _).obj F)))

/- Remark 60.24.7 (Specific boundedness) (2): for a separated source covered by `q`
affines, crystalline cohomology vanishes above `q + e`. -/
@[stacks 07MR] #check
  (AlgebraicGeometry.Scheme.Crystalline.isZero_of_affineCover_add_embeddingDimension :
    ∀ {p : ℕ} [Fact p.Prime] (B : Base.{u} p)
    [Unique B.ideal.subscheme] [FinitePresentation B.sourceToClosed]
    [HasSheafify
      (smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
        B.source B.sourceToClosed B.prime_nilpotent) AddCommGrpCat.{u}]
    [HasExt.{v} (Sheaf
      (smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
        B.source B.sourceToClosed B.prime_nilpotent) AddCommGrpCat.{u})]
    [∀ U : smallCrystallineSite B.scheme B.ideal B.dividedPowers B.compatible
        B.source B.sourceToClosed,
      HasWeakSheafify
        ((smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
          B.source B.sourceToClosed B.prime_nilpotent).over U) AddCommGrpCat.{u}]
    [∀ U : smallCrystallineSite B.scheme B.ideal B.dividedPowers B.compatible
        B.source B.sourceToClosed,
      ((smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
        B.source B.sourceToClosed B.prime_nilpotent).over U).WEqualsLocallyBijective
          AddCommGrpCat.{u}]
    [B.source.IsSeparated] (𝒰 : B.source.AffineOpenCover.{u}) [Fintype 𝒰.I₀]
    (F : SheafOfModules.{u}
      (smallCrystallineStructureSheaf B.ideal B.dividedPowers B.compatible B.toSpec
        B.sourceToClosed B.prime_nilpotent))
    [IsCrystalInQuasiCoherentModules F]
    (q e i : ℕ) (hq : Fintype.card 𝒰.I₀ = q)
    (h_emb : B.sourceToClosed.HasEmbeddingDimensionLE e) (hi : q + e < i),
    IsZero
      ((Sheaf.functorH
        (smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
          B.source B.sourceToClosed B.prime_nilpotent) i).obj
        ((SheafOfModules.toSheaf _).obj F)))
