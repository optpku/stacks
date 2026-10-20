/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.AdditiveGroup

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory
open AlgebraicGeometry
open scoped AlgebraicGeometry CategoryTheory.MonObj

universe u

/- Example 39.5.3 (Additive group scheme) (1): the integral model of the additive group scheme is
`Spec (ℤ[X])`. -/
@[stacks 022V] #check (AlgebraicGeometry.AdditiveGroup.integralModelIso :
  (AlgebraicGeometry.AdditiveGroup.groupScheme (Spec (.of ℤ))).X.left ≅
    Spec (.of (Polynomial ℤ)))

/- Example 39.5.3 (Additive group scheme) (2): the affine line over every scheme is a canonical
commutative group scheme. -/
@[stacks 022V] #check (AlgebraicGeometry.AdditiveGroup.groupScheme :
  (S : Scheme.{u}) → CommGrp (Over S))

/- Example 39.5.3 (Additive group scheme) (3): addition pulls a coordinate back to the sum of its
pullbacks along the two projections. -/
@[stacks 022V] #check (AlgebraicGeometry.AffineSpace.add_appTop_coord :
  (n : Type u) → (S : Scheme.{u}) → (i : n) →
    μ[Scheme.asOver (𝔸(n; S)) S].left.appTop (AlgebraicGeometry.AffineSpace.coord S i) =
      (fst (Scheme.asOver (𝔸(n; S)) S) (Scheme.asOver (𝔸(n; S)) S)).left.appTop
          (AlgebraicGeometry.AffineSpace.coord S i) +
        (snd (Scheme.asOver (𝔸(n; S)) S) (Scheme.asOver (𝔸(n; S)) S)).left.appTop
          (AlgebraicGeometry.AffineSpace.coord S i))

/- Example 39.5.3 (Additive group scheme) (4): the additive group scheme is compatible with base
change as a commutative group object. -/
@[stacks 022V] #check (AlgebraicGeometry.AdditiveGroup.baseChangeIso :
  {S T : Scheme.{u}} → (f : S ⟶ T) →
    AlgebraicGeometry.AdditiveGroup.groupScheme S ≅
      (Over.pullback f).mapCommGrp.obj (AlgebraicGeometry.AdditiveGroup.groupScheme T))

/- Example 39.5.3 (Additive group scheme) (5): the additive group scheme represents the
group-valued functor of global sections. -/
@[stacks 022V] #check (AlgebraicGeometry.AdditiveGroup.representingIso :
  (S : Scheme.{u}) →
    CategoryTheory.yonedaGrp.obj (AlgebraicGeometry.AdditiveGroup.groupScheme S).toGrp ≅
      AlgebraicGeometry.AdditiveGroup.points S)
