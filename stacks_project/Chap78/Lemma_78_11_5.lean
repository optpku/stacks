/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import stacks_project.Chap79.«79_3_0_2_Pullback»
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Pullback
import stacks_project.Chap78.Definition_78_11_1_Groupoid
import StacksCheckRecall

open CategoryTheory Limits

universe u

/- Lemma 78.11.5 (1): The target comparison commutes with the first projections;
Stacks `pr₀` is `pullback.fst` and the left vertical map is `targetComparison`. -/
@[stacks 0450] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.targetComparison_fst :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
      (G : AlgebraicGeometry.GroupoidAlgebraicSpace B),
      G.targetComparison ≫ pullback.fst G.s G.t = pullback.fst G.t G.t)

/- Lemma 78.11.5 (2): Composition after the target comparison is the second projection;
Stacks `pr₁` is `pullback.snd`. -/
@[stacks 0450] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.leftDivision_cancel :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
      (G : AlgebraicGeometry.GroupoidAlgebraicSpace B),
      G.targetComparison ≫ G.c = pullback.snd G.t G.t)

/- Lemma 78.11.5 (3): The two top rows are isomorphic via the displayed vertical maps;
the left vertical map is `(pr₀, c ∘ (i, 1))`. -/
@[stacks 0450] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.targetComparisonIso :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
      (G : AlgebraicGeometry.GroupoidAlgebraicSpace B),
      pullback G.t G.t ≅ pullback G.s G.t)

#check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.targetComparisonIso_hom :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
      (G : AlgebraicGeometry.GroupoidAlgebraicSpace B),
      G.targetComparisonIso.hom = G.targetComparison)

/- Lemma 78.11.5 (4): The upper lower-left square, with composition and the second
projection, is cartesian. -/
@[stacks 0450] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.compSndIsPullback :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
      (G : AlgebraicGeometry.GroupoidAlgebraicSpace B),
      IsPullback G.c (pullback.snd G.s G.t) G.s G.s)

/- Lemma 78.11.5 (5): The lower lower-left square, formed by the two pullback
projections, is cartesian. -/
@[stacks 0450] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.fstSndIsPullback :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
      (G : AlgebraicGeometry.GroupoidAlgebraicSpace B),
      IsPullback (pullback.fst G.s G.t) (pullback.snd G.s G.t) G.s G.t)
