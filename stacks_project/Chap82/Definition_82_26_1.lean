/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.BivariantClass

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Definition 82.26.1: In Situation 82.2.1, for a morphism `f : X ⟶ Y` of
good algebraic spaces over `B` and `p ∈ ℤ`, a bivariant class of degree `p`
for `f` is a rule assigning to every good `Y' ⟶ Y` over `B` and every `k` an
additive cap `c ∩ - : CH_k(Y') ⟶ CH_{k - p}(X')` on a cartesian square
`X' = Y' ×_Y X`, compatible with proper pushforward, flat pullback of fixed
relative dimension `r`, and refined Gysin along a zero-scheme
`(L', s', i' : D' ⟶ Y')` and its pullback to `X'`. The type of all such
classes is `A^p(X ⟶ Y)`. -/
@[stacks 0ERJ] #check (AlgebraicGeometry.AlgebraicSpace.BivariantClass :
  ∀ {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (f : X ⟶ Y) [QuasiSeparated (f ≫ pY)] [LocallyOfFiniteType (f ≫ pY)]
    (p : ℤ), Type (u + 1))
