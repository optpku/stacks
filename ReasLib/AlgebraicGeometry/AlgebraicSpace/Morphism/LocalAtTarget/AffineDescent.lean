/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.AffineDescent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sites.FpqcPrecoverage

/-!
# Affine coproduct-and-descent criterion for fpqc locality

A morphism property of algebraic spaces that is stable under binary and nullary
coproducts, detected by affine-scheme base change, and descending along surjective
flat morphisms of affine schemes is fpqc local on the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace.AffineDescendsAlong

/-- A morphism property of algebraic spaces over a scheme that is stable under
binary and nullary coproducts, detected by all affine-scheme base changes, and
descending along surjective flat morphisms of affine schemes is fpqc local on
the target. -/
instance isLocalAtTargetFpqc {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
    [P.IsStableUnderCoproductsOfShape WalkingPair] [AffineLocalAtTarget P]
    [P.IsStableUnderCoproductsOfShape Empty]
    [AffineDescendsAlong P (@Flat S : MorphismProperty (AlgebraicSpace S))] :
    P.IsLocalAtTarget (fpqcPrecoverage S) := sorry

end AlgebraicGeometry.AlgebraicSpace.AffineDescendsAlong
