/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Affine.Diagonal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection.Regular
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import stacks_project.Chap42.Lemma_42_59_12_IntersectionProduct
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.BivariantClass AlgebraicGeometry.ChowGroup
open AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle
open AlgebraicGeometry.Scheme.VectorBundleK0
open scoped Topology

noncomputable section

universe u

/- Lemma 42.59.12 (1): a locally finite-type morphism of regular schemes is a local
complete intersection morphism. -/
@[stacks 0FF9] #check
  (AlgebraicGeometry.LocallyOfFiniteType.isLocalCompleteIntersection_of_regular :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.LocallyOfFiniteType f] [AlgebraicGeometry.Scheme.Regular X]
      [AlgebraicGeometry.Scheme.Regular Y],
      AlgebraicGeometry.LocallyOfType RingHom.IsLocalCompleteIntersection f)

/-- Lemma 42.59.12 (2): in Situation 42.7.1, if `f : X ⟶ Y` is a morphism of schemes
locally of finite type over `S` with `X` and `Y` quasi-compact, regular, of affine
diagonal, and finite dimension, and the Gysin map of `f` exists, then
`f^!(α · β) = f^!α · f^!β` in `CH^*(X) ⊗ Q`, where `·` is the Section 42.58
intersection product. -/
@[stacks 0FF9]
theorem gysin_rationalIntersectionProduct
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [CompactSpace X.left] [CompactSpace Y.left]
    [Scheme.Regular X.left] [Scheme.Regular Y.left]
    [IsAffineHom (prod.lift (𝟙 X.left) (𝟙 X.left))]
    [IsAffineHom (prod.lift (𝟙 Y.left) (𝟙 Y.left))]
    (f : X ⟶ Y) (hf : HasGysinMap f)
    {P : Over S} [LocallyOfFiniteType P.hom]
    (ι : X ⟶ P) (σ : P ⟶ Y) (hι : IsImmersion ι.left)
    [IsClosedImmersion ι.left] [IsRegularImmersion ι.left] [hσ : Smooth σ.left]
    (hfac : ι ≫ σ = f) (t : ℕ) [Scheme.Hom.RelativeDimension σ.left t] (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf ι.left)]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf ι.left) ≅
      Scheme.Hom.conormalSheaf ι.left)
    (D : ClosedSpecialization δ X.hom P.hom ι.left (Over.w ι)
      (ofNormalSheaf ι.left r e))
    (hXdim : topologicalKrullDim X.left < ⊤)
    (hYdim : topologicalKrullDim Y.left < ⊤)
    (classes : ChernClass.Theory δ Y.hom)
    (α β : TensorProduct ℤ (Scheme.VectorBundleK0 Y.left) ℚ) :
    gysinMap δ f ι σ hι hfac t r e D
        (rationalIntersectionProduct δ Y classes hYdim α β) =
      rationalIntersectionProduct δ X (classes.reanchor X) hXdim
        (pullbackRational f.left α) (pullbackRational f.left β) :=
  sorry
