/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocalAtTarget.AffineDescent
import StacksCheckRecall

/-!
# Affine coproduct-and-descent criterion for fpqc locality

A morphism property of algebraic spaces that is stable under binary and nullary
coproducts, detected by affine-scheme base change, and descending along surjective
flat morphisms of affine schemes is fpqc local on the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits MorphismProperty

universe u

/- 041J::statement_repair::1 — Lemma 74.10.4: affine detection and surjective flat
affine descent imply fpqc locality under binary and nullary coproduct closure.
The nullary premise is the authorized correction preserving empty fpqc covers. -/
@[stacks 041J] #check
  (AlgebraicGeometry.AlgebraicSpace.AffineDescendsAlong.isLocalAtTargetFpqc :
    ∀ {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
      [P.IsStableUnderCoproductsOfShape WalkingPair] [AffineLocalAtTarget P]
      [P.IsStableUnderCoproductsOfShape Empty]
      [AffineDescendsAlong P (@Flat S : MorphismProperty (AlgebraicSpace S))],
      P.IsLocalAtTarget (fpqcPrecoverage S))
