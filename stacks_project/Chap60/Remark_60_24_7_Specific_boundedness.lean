/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.TangentSpace.EmbeddingDimension
public import stacks_project.Chap60.Definition_60_9_1
public import stacks_project.Chap60.Definition_60_11_3_Crystal
public import stacks_project.Chap60.Lemma_60_25_4_Linearization
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Crystalline
open SheafOfModules

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A morphism `f : X ⟶ Y` has embedding dimension at most `e` when the relative
tangent dimension of `f` at every point of `X` is at most `e`. -/
def HasEmbeddingDimensionLE {X Y : Scheme.{u}} (f : X ⟶ Y) (e : ℕ) : Prop :=
  ∀ x : X, tangentDimensionAt f x ≤ e

/-- `HasEmbeddingDimensionLE f e` is the pointwise bound
`tangentDimensionAt f x ≤ e` at every point of `X`. -/
theorem hasEmbeddingDimensionLE_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (e : ℕ) :
    f.HasEmbeddingDimensionLE e ↔ ∀ x : X, tangentDimensionAt f x ≤ e :=
  sorry

/-- A morphism which is smooth of relative dimension `e` has embedding dimension
at most `e`. -/
theorem hasEmbeddingDimensionLE_of_smoothOfRelativeDimension
    {X Y : Scheme.{u}} (f : X ⟶ Y) (e : ℕ) [SmoothOfRelativeDimension e f] :
    f.HasEmbeddingDimensionLE e :=
  sorry

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Crystalline

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {S : Scheme.{u}} (I : S.IdealSheafData)
variable (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
variable (h_compatible :
  ∀ (V : S.affineOpens) (f : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
      (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
variable (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
variable [Unique I.subscheme] [FinitePresentation x₀]
variable [HasSheafify (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
    AddCommGrpCat.{u}]
variable [HasExt (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
    AddCommGrpCat.{u})]
variable [HasWeakSheafify (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
    AddCommGrpCat.{u}]
variable [(smallCrystallineTopology p S I γ h_compatible s X x₀ h_p).WEqualsLocallyBijective
    AddCommGrpCat.{u}]
variable [∀ U : smallCrystallineSite S I γ h_compatible X x₀,
    HasWeakSheafify
      ((smallCrystallineTopology p S I γ h_compatible s X x₀ h_p).over U) AddCommGrpCat.{u}]
variable [∀ U : smallCrystallineSite S I γ h_compatible X x₀,
    ((smallCrystallineTopology p S I γ h_compatible s X x₀ h_p).over U).WEqualsLocallyBijective
      AddCommGrpCat.{u}]

/-- Remark 60.24.7 (Specific boundedness) (1): in Situation 60.7.5, let `F` be a
crystal in quasi-coherent `𝒪_{X/S}`-modules. If `S₀` has a unique point, `X ⟶ S₀`
is of finite presentation, `dim X = d`, and `X / S₀` has embedding dimension `e`,
then `H^i(Cris(X/S), F) = 0` for `i > d + e`. -/
@[stacks 07MR]
theorem isZero_of_dim_add_embeddingDimension
    (F : SheafOfModules (smallCrystallineStructureSheaf I γ h_compatible s x₀ h_p))
    [IsCrystalInQuasiCoherentModules F]
    (d e i : ℕ) (h_dim : topologicalKrullDim X = (d : WithBot ℕ∞))
    (h_emb : x₀.HasEmbeddingDimensionLE e) (hi : d + e < i) :
    IsZero
      ((Sheaf.functorH (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) i).obj
        ((SheafOfModules.toSheaf _).obj F)) :=
  sorry

/-- Remark 60.24.7 (Specific boundedness) (2): in Situation 60.7.5, let `F` be a
crystal in quasi-coherent `𝒪_{X/S}`-modules. If `S₀` has a unique point, `X ⟶ S₀`
is of finite presentation, `X` is separated and covered by `q` affines, and
`X / S₀` has embedding dimension `e`, then `H^i(Cris(X/S), F) = 0` for
`i > q + e`. -/
@[stacks 07MR]
theorem isZero_of_affineCover_add_embeddingDimension
    [X.IsSeparated] (𝒰 : X.AffineOpenCover.{u}) [Fintype 𝒰.I₀]
    (F : SheafOfModules (smallCrystallineStructureSheaf I γ h_compatible s x₀ h_p))
    [IsCrystalInQuasiCoherentModules F]
    (q e i : ℕ) (hq : Fintype.card 𝒰.I₀ = q)
    (h_emb : x₀.HasEmbeddingDimensionLE e) (hi : q + e < i) :
    IsZero
      ((Sheaf.functorH (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) i).obj
        ((SheafOfModules.toSheaf _).obj F)) :=
  sorry

end AlgebraicGeometry.Scheme.Crystalline
