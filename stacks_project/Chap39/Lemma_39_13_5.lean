/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Pullback
import StacksCheckRecall

open CategoryTheory Limits

universe u

/- Lemma 39.13.5 (1): The target comparison commutes with the first projections. -/
@[stacks 03C6] #check
  (AlgebraicGeometry.GroupoidScheme.targetComparison_fst :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S),
      G.targetComparison ≫ pullback.fst G.s G.t = pullback.fst G.t G.t)

/- Lemma 39.13.5 (2): Composition after the target comparison is the second projection. -/
@[stacks 03C6] #check
  (AlgebraicGeometry.GroupoidScheme.leftDivision_cancel :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S),
      G.targetComparison ≫ G.c = pullback.snd G.t G.t)

/- Lemma 39.13.5 (3): The common-target and composable-pair pullbacks are canonically
isomorphic through the displayed vertical maps. -/
@[stacks 03C6] #check
  (AlgebraicGeometry.GroupoidScheme.targetComparisonIso :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S),
      pullback G.t G.t ≅ pullback G.s G.t)

#check
  (AlgebraicGeometry.GroupoidScheme.targetComparisonIso_hom :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S),
      G.targetComparisonIso.hom = G.targetComparison)

/- Lemma 39.13.5 (4): The lower square with composition and source is cartesian. -/
@[stacks 03C6] #check
  (AlgebraicGeometry.GroupoidScheme.compSndIsPullback :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S),
      IsPullback G.c (pullback.snd G.s G.t) G.s G.s)

/- Lemma 39.13.5 (5): The lower square formed by the two pullback projections is cartesian. -/
@[stacks 03C6] #check
  (AlgebraicGeometry.GroupoidScheme.fstSndIsPullback :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S),
      IsPullback (pullback.fst G.s G.t) (pullback.snd G.s G.t) G.s G.t)
