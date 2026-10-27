/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.Rational.Pushforward
public import ReasLib.AlgebraicGeometry.BivariantClass.Gysin.Intersection

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ChowGroup

universe u

namespace AlgebraicGeometry.BivariantClass

/-- Proper pushforward between quasi-compact regular finite-dimensional schemes with affine
diagonal satisfies the projection formula for rational intersection products whenever the
Gysin map exists. -/
theorem gysin_projection_formula
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [CompactSpace X.left] [CompactSpace Y.left]
    [Scheme.Regular X.left] [Scheme.Regular Y.left]
    [IsAffineHom (prod.lift (𝟙 X.left) (𝟙 X.left))]
    [IsAffineHom (prod.lift (𝟙 Y.left) (𝟙 Y.left))]
    (f : X ⟶ Y) (hf : HasGysinMap f) [IsProper f.left]
    (hXdim : topologicalKrullDim X.left < ⊤)
    (hYdim : topologicalKrullDim Y.left < ⊤)
    (α : rationalChow δ X) (β : rationalChow δ Y) :
    rationalPushforward δ f
        (regularIntersectionProduct δ X (ChernClass.Theory.canonical δ X.hom) hXdim α
          (gysinMapRegular δ f hXdim hYdim (ChernClass.Theory.canonical δ Y.hom) β)) =
      regularIntersectionProduct δ Y (ChernClass.Theory.canonical δ Y.hom) hYdim
        (rationalPushforward δ f α) β := sorry

end AlgebraicGeometry.BivariantClass
