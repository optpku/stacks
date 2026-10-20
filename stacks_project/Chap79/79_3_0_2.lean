module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Pullback
import StacksCheckRecall

universe u

open CategoryTheory AlgebraicGeometry Limits

/- 79.3.0.2: The map `(pr₀, c ∘ (i, 1))` identifies `pullback G.t G.t` with
`pullback G.s G.t`. -/
@[stacks 0451] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.targetComparisonIso :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      [CategoryTheory.Limits.HasPullbacks (AlgebraicGeometry.AlgebraicSpace S)]
      {B : AlgebraicGeometry.AlgebraicSpace S}
      (G : AlgebraicGeometry.GroupoidAlgebraicSpace B),
      CategoryTheory.Limits.pullback G.t G.t ≅ CategoryTheory.Limits.pullback G.s G.t)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.targetComparison_fst :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    [CategoryTheory.Limits.HasPullbacks (AlgebraicGeometry.AlgebraicSpace S)]
    {B : AlgebraicGeometry.AlgebraicSpace S}
    (G : AlgebraicGeometry.GroupoidAlgebraicSpace B),
    G.targetComparison ≫ CategoryTheory.Limits.pullback.fst G.s G.t =
      CategoryTheory.Limits.pullback.fst G.t G.t)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.targetComparison_snd :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    [CategoryTheory.Limits.HasPullbacks (AlgebraicGeometry.AlgebraicSpace S)]
    {B : AlgebraicGeometry.AlgebraicSpace S}
    (G : AlgebraicGeometry.GroupoidAlgebraicSpace B),
    G.targetComparison ≫ CategoryTheory.Limits.pullback.snd G.s G.t = G.leftDivision)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.leftDivision_cancel :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    [CategoryTheory.Limits.HasPullbacks (AlgebraicGeometry.AlgebraicSpace S)]
    {B : AlgebraicGeometry.AlgebraicSpace S}
    (G : AlgebraicGeometry.GroupoidAlgebraicSpace B),
    G.targetComparison ≫ G.c = CategoryTheory.Limits.pullback.snd G.t G.t)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.compSndIsPullback :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    [CategoryTheory.Limits.HasPullbacks (AlgebraicGeometry.AlgebraicSpace S)]
    {B : AlgebraicGeometry.AlgebraicSpace S}
    (G : AlgebraicGeometry.GroupoidAlgebraicSpace B),
    IsPullback G.c
      (CategoryTheory.Limits.pullback.snd G.s G.t) G.s G.s)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.fstSndIsPullback :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    [CategoryTheory.Limits.HasPullbacks (AlgebraicGeometry.AlgebraicSpace S)]
    {B : AlgebraicGeometry.AlgebraicSpace S}
    (G : AlgebraicGeometry.GroupoidAlgebraicSpace B),
    IsPullback
      (CategoryTheory.Limits.pullback.fst G.s G.t)
      (CategoryTheory.Limits.pullback.snd G.s G.t) G.s G.t)
