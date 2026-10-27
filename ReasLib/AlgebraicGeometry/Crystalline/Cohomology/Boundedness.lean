/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.TangentSpace.Bound
public import ReasLib.AlgebraicGeometry.Crystalline.Base
public import ReasLib.AlgebraicGeometry.Crystalline.StructureSheaf.Small
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Crystal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Topology.KrullDimension

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom SheafOfModules

universe u v

namespace AlgebraicGeometry.Scheme.Crystalline

variable {p : ℕ} [Fact p.Prime] (B : Base.{u} p)
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

/-- Over a one-point closed base, a finitely presented scheme of dimension `d` and relative
embedding dimension at most `e` has crystalline cohomology zero above `d + e` with coefficients
in any crystal in quasi-coherent modules. -/
theorem isZero_of_dim_add_embeddingDimension
    (F : SheafOfModules.{u}
      (smallCrystallineStructureSheaf B.ideal B.dividedPowers B.compatible B.toSpec
        B.sourceToClosed B.prime_nilpotent))
    [IsCrystalInQuasiCoherentModules F]
    (d e i : ℕ) (h_dim : topologicalKrullDim B.source = (d : WithBot ℕ∞))
    (h_emb : B.sourceToClosed.HasEmbeddingDimensionLE e) (hi : d + e < i) :
    IsZero
      ((Sheaf.functorH
        (smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
          B.source B.sourceToClosed B.prime_nilpotent) i).obj
        ((SheafOfModules.toSheaf _).obj F)) := sorry

/-- Over a one-point closed base, a separated finitely presented scheme covered by `q` affine
opens and of relative embedding dimension at most `e` has crystalline cohomology zero above
`q + e` with coefficients in any crystal in quasi-coherent modules. -/
theorem isZero_of_affineCover_add_embeddingDimension
    [B.source.IsSeparated] (𝒰 : B.source.AffineOpenCover.{u}) [Fintype 𝒰.I₀]
    (F : SheafOfModules.{u}
      (smallCrystallineStructureSheaf B.ideal B.dividedPowers B.compatible B.toSpec
        B.sourceToClosed B.prime_nilpotent))
    [IsCrystalInQuasiCoherentModules F]
    (q e i : ℕ) (hq : Fintype.card 𝒰.I₀ = q)
    (h_emb : B.sourceToClosed.HasEmbeddingDimensionLE e) (hi : q + e < i) :
    IsZero
      ((Sheaf.functorH
        (smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
          B.source B.sourceToClosed B.prime_nilpotent) i).obj
        ((SheafOfModules.toSheaf _).obj F)) := sorry

end AlgebraicGeometry.Scheme.Crystalline
