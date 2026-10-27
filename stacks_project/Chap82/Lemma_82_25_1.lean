/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.FlatPullback.AffineFiber
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 82.25.1: A quasi-compact flat morphism of good algebraic spaces whose
residue-field fibres are affine spaces induces a surjective Chow pullback. -/
@[stacks 0ERG] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.chowFlatPullback_surjective :
    ∀ {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [QuasiCompact f] [Flat f] [RelativeDimension f r]
    [IsDecent Y] (hf : f ≫ pY = pX)
    (h_fiber : ∀ y : Points Y, Hom.IsAffineSpaceFiber f r y) (k : ℤ),
    Function.Surjective (AlgebraicGeometry.AlgebraicSpace.ChowGroup.flatPullback pY pX δ f r hf k))
