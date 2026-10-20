module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Pullback

/-!
# Pullback comparisons for groupoids in algebraic spaces

This module exposes typed compatibility checks for the reusable comparison API.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.leftDivisionCondition :
  ∀ {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S},
    (G : GroupoidAlgebraicSpace B) →
      (pullback.fst G.t G.t ≫ G.i) ≫ G.s = pullback.snd G.t G.t ≫ G.t)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.leftDivision :
  ∀ {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S},
    (G : GroupoidAlgebraicSpace B) → pullback G.t G.t ⟶ G.R)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.leftDivision_source :
  ∀ {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S},
    (G : GroupoidAlgebraicSpace B) →
      G.leftDivision ≫ G.s = pullback.snd G.t G.t ≫ G.s)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.leftDivision_target :
  ∀ {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S},
    (G : GroupoidAlgebraicSpace B) →
      G.leftDivision ≫ G.t = pullback.fst G.t G.t ≫ G.s)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.targetComparisonCondition :
  ∀ {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S},
    (G : GroupoidAlgebraicSpace B) →
      pullback.fst G.t G.t ≫ G.s = G.leftDivision ≫ G.t)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.targetComparison :
  ∀ {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S},
    (G : GroupoidAlgebraicSpace B) → pullback G.t G.t ⟶ pullback G.s G.t)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.targetComparison_fst :
  ∀ {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S},
    (G : GroupoidAlgebraicSpace B) →
      G.targetComparison ≫ pullback.fst G.s G.t = pullback.fst G.t G.t)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.targetComparison_snd :
  ∀ {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S},
    (G : GroupoidAlgebraicSpace B) →
      G.targetComparison ≫ pullback.snd G.s G.t = G.leftDivision)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.leftDivision_cancel :
  ∀ {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S},
    (G : GroupoidAlgebraicSpace B) →
      G.targetComparison ≫ G.c = pullback.snd G.t G.t)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.targetComparisonInvCondition :
  ∀ {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S},
    (G : GroupoidAlgebraicSpace B) →
      pullback.fst G.s G.t ≫ G.t = G.c ≫ G.t)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.targetComparisonInv :
  ∀ {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S},
    (G : GroupoidAlgebraicSpace B) → pullback G.s G.t ⟶ pullback G.t G.t)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.targetComparisonInv_fst :
  ∀ {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S},
    (G : GroupoidAlgebraicSpace B) →
      G.targetComparisonInv ≫ pullback.fst G.t G.t = pullback.fst G.s G.t)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.targetComparisonInv_snd :
  ∀ {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S},
    (G : GroupoidAlgebraicSpace B) →
      G.targetComparisonInv ≫ pullback.snd G.t G.t = G.c)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.targetComparison_hom_inv :
  ∀ {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S},
    (G : GroupoidAlgebraicSpace B) →
      G.targetComparison ≫ G.targetComparisonInv = 𝟙 (pullback G.t G.t))

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.targetComparison_inv_hom :
  ∀ {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S},
    (G : GroupoidAlgebraicSpace B) →
      G.targetComparisonInv ≫ G.targetComparison = 𝟙 (pullback G.s G.t))

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.targetComparisonIso :
  ∀ {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S},
    (G : GroupoidAlgebraicSpace B) → pullback G.t G.t ≅ pullback G.s G.t)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.targetComparisonIso_hom :
  ∀ {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S},
    (G : GroupoidAlgebraicSpace B) → G.targetComparisonIso.hom = G.targetComparison)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.targetComparisonIso_inv :
  ∀ {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S},
    (G : GroupoidAlgebraicSpace B) → G.targetComparisonIso.inv = G.targetComparisonInv)
