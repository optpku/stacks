module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap74.Lemma_74_10_4_Affine
public import stacks_project.Chap74.Lemma_74_11_6_Precoverage

/-!
# Affine coproduct-and-descent criterion for fpqc locality

A morphism property of algebraic spaces that is stable under binary coproducts,
detected by affine-scheme base change, and descending along surjective flat
morphisms of affine schemes is fpqc local on the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace.AffineDescendsAlong

/-- Lemma 74.10.4: Let `S` be a scheme and `P` a property of morphisms of
algebraic spaces over `S`. If morphisms in `P` are stable under binary
coproducts, a morphism has `P` if and only if every base change along a
morphism from an affine scheme over `S` has `P`, and `P` descends along
surjective flat morphisms of affine schemes over `S`, then `P` is fpqc local
on the target. -/
@[stacks 041J]
instance isLocalAtTargetFpqc {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
    [P.IsStableUnderCoproductsOfShape WalkingPair] [AffineLocalAtTarget P]
    [AffineDescendsAlong P (@Flat S : MorphismProperty (AlgebraicSpace S))] :
    P.IsLocalAtTarget (fpqcPrecoverage S) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.AffineDescendsAlong
