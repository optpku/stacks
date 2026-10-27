/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Gysin.ProjectionFormula
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ChowGroup AlgebraicGeometry.BivariantClass

universe u

/- Lemma 42.59.13 (1): the general regular-scheme theorem applies to `f.left` in
Situation 42.7.1, where `X` and `Y` are locally of finite type over `S`, quasi-compact,
regular, finite-dimensional, and have affine diagonal. -/
@[stacks 0FFA] #check (AlgebraicGeometry.LocallyOfFiniteType.isLocalCompleteIntersection_of_regular :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    [Scheme.Regular X] [Scheme.Regular Y],
    LocallyOfType RingHom.IsLocalCompleteIntersection f)

/- Lemma 42.59.13 (2): if the Gysin map exists and `f` is proper, then
`f_*(α · f^!β) = f_*α · β` for all rational Chow classes. -/
@[stacks 0FFA] #check (AlgebraicGeometry.BivariantClass.gysin_projection_formula :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [CompactSpace X.left] [CompactSpace Y.left]
    [Scheme.Regular X.left] [Scheme.Regular Y.left]
    [IsAffineHom (prod.lift (𝟙 X.left) (𝟙 X.left))]
    [IsAffineHom (prod.lift (𝟙 Y.left) (𝟙 Y.left))]
    (f : X ⟶ Y) (hf : HasGysinMap f) [IsProper f.left]
    (hXdim : topologicalKrullDim X.left < ⊤)
    (hYdim : topologicalKrullDim Y.left < ⊤)
    (α : rationalChow δ X) (β : rationalChow δ Y),
    rationalPushforward δ f
        (regularIntersectionProduct δ X (ChernClass.Theory.canonical δ X.hom) hXdim α
          (gysinMapRegular δ f hXdim hYdim (ChernClass.Theory.canonical δ Y.hom) β)) =
      regularIntersectionProduct δ Y (ChernClass.Theory.canonical δ Y.hom) hYdim
        (rationalPushforward δ f α) β)
