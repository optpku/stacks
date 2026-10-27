/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.BivariantClass.FlatPullback

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 82.26.5: A flat morphism of good algebraic spaces over `B` of relative
 dimension `r` defines a bivariant class of degree `-(r : ℤ)`, acting on each
 cartesian base change by flat pullback on Chow groups. -/
@[stacks 0ERN] #check (AlgebraicGeometry.AlgebraicSpace.BivariantClass.flatPullback :
  ∀ {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (f : X ⟶ Y) [QuasiSeparated (f ≫ pY)] [LocallyOfFiniteType (f ≫ pY)]
    (r : ℕ) [Flat f] [RelativeDimension f r],
    AlgebraicGeometry.AlgebraicSpace.BivariantClass δ pY f (-(r : ℤ)))

