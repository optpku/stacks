/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Gysin.Intersection
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.BivariantClass AlgebraicGeometry.ChowGroup
open AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle
open AlgebraicGeometry.Scheme.VectorBundleK0
open scoped Topology

noncomputable section

universe u

/- Lemma 42.59.12 (1): A locally finite-type morphism of regular schemes is a local complete
intersection morphism. -/
@[stacks 0FF9] #check
  (AlgebraicGeometry.LocallyOfFiniteType.isLocalCompleteIntersection_of_regular :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.LocallyOfFiniteType f] [AlgebraicGeometry.Scheme.Regular X]
      [AlgebraicGeometry.Scheme.Regular Y],
      AlgebraicGeometry.LocallyOfType RingHom.IsLocalCompleteIntersection f)

/- Lemma 42.59.12 (2): Gysin pullback preserves the rational intersection product for
quasi-compact regular finite-dimensional schemes with affine diagonal. -/
@[stacks 0FF9] #check
  (AlgebraicGeometry.BivariantClass.gysin_rationalIntersectionProduct :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
      {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
      [CompactSpace X.left] [CompactSpace Y.left]
      [Scheme.Regular X.left] [Scheme.Regular Y.left]
      [IsAffineHom (prod.lift (𝟙 X.left) (𝟙 X.left))]
      [IsAffineHom (prod.lift (𝟙 Y.left) (𝟙 Y.left))]
      (f : X ⟶ Y)
      (hXdim : topologicalKrullDim X.left < ⊤)
      (hYdim : topologicalKrullDim Y.left < ⊤)
      (hf : HasGysinMap f)
      (α β : rationalChow δ Y),
      gysinMapRegular δ f hXdim hYdim (ChernClass.Theory.canonical δ Y.hom)
        (regularIntersectionProduct δ Y (ChernClass.Theory.canonical δ Y.hom) hYdim α β) =
          regularIntersectionProduct δ X (ChernClass.Theory.canonical δ X.hom) hXdim
            (gysinMapRegular δ f hXdim hYdim (ChernClass.Theory.canonical δ Y.hom) α)
            (gysinMapRegular δ f hXdim hYdim (ChernClass.Theory.canonical δ Y.hom) β))
