/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Translation
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.GroupoidAlgebraicSpace

noncomputable section

universe u

/- Lemma 79.9.7 (1): In Situation 79.9.2, an underlying arrow whose source
and target composites are automorphisms determines an automorphism of the arrow
space. Normalization by the inverse source automorphism is the precise translation
used by the cited proof; the construction works for any groupoid in algebraic spaces. -/
@[stacks 06E3] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.isIso_leftTranslationAt :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
      (r : G.U.left ⟶ G.R.left) [IsIso (r ≫ G.s.left)] [IsIso (r ≫ G.t.left)],
      IsIso (G.leftTranslationAt r))

/- Lemma 79.9.7 (2): Translation sends the identity section to the normalized
source section. Recovery of the original arrow is through the source automorphism,
not an unqualified equality G.e ≫ translation = r. -/
@[stacks 06E3] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.leftTranslationAt_recoversArrow :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
      (r : G.U.left ⟶ G.R.left) [IsIso (r ≫ G.s.left)],
      (r ≫ G.s.left) ≫ G.e.left ≫ (G.leftTranslationAt r).left = r)
