/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.Pullback
public import stacks_project.Chap65.Lemma_65_7_3_Pullback

open AlgebraicGeometry CategoryTheory

universe u

#check (@AlgebraicGeometry.AlgebraicSpace.PreRelation.pullback :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
    [CategoryTheory.Limits.HasPullbacks (AlgebraicGeometry.AlgebraicSpace S)]
    {U U' : Over B},
    AlgebraicGeometry.AlgebraicSpace.PreRelation U → (U' ⟶ U) →
      AlgebraicGeometry.AlgebraicSpace.PreRelation U')

#check (@AlgebraicGeometry.AlgebraicSpace.PreRelation.pullback_left :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
    [CategoryTheory.Limits.HasPullbacks (AlgebraicGeometry.AlgebraicSpace S)]
    {U U' : Over B} (P : AlgebraicGeometry.AlgebraicSpace.PreRelation U)
    (g : U' ⟶ U),
    (P.pullback g).left = CategoryTheory.Limits.pullback P.hom
      (CategoryTheory.Limits.prod.map g g))

#check (@AlgebraicGeometry.AlgebraicSpace.PreRelation.pullback_hom :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
    [CategoryTheory.Limits.HasPullbacks (AlgebraicGeometry.AlgebraicSpace S)]
    {U U' : Over B} (P : AlgebraicGeometry.AlgebraicSpace.PreRelation U)
    (g : U' ⟶ U),
    (P.pullback g).hom = CategoryTheory.Limits.pullback.snd P.hom
      (CategoryTheory.Limits.prod.map g g))

#check (@AlgebraicGeometry.AlgebraicSpace.PreRelation.pullback_pointRel_iff :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
    [CategoryTheory.Limits.HasPullbacks (AlgebraicGeometry.AlgebraicSpace S)]
    {U U' : Over B} (P : AlgebraicGeometry.AlgebraicSpace.PreRelation U)
    (g : U' ⟶ U) {T : Over S} (τ : AlgebraicGeometry.AlgebraicSpace.ofOver T ⟶ B)
    (x y : Over.mk τ ⟶ U'),
    (P.pullback g).pointRel (Over.mk τ) x y ↔
      P.pointRel (Over.mk τ) (x ≫ g) (y ≫ g))

#check (@AlgebraicGeometry.AlgebraicSpace.PreRelation.instMonoHomPullback :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
    [CategoryTheory.Limits.HasPullbacks (AlgebraicGeometry.AlgebraicSpace S)]
    {U U' : Over B} (P : AlgebraicGeometry.AlgebraicSpace.PreRelation U)
    (g : U' ⟶ U) [Mono P.hom], Mono (P.pullback g).hom)

#check (@AlgebraicGeometry.AlgebraicSpace.PreRelation.IsPreEquivalence.pullback :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
    [CategoryTheory.Limits.HasPullbacks (AlgebraicGeometry.AlgebraicSpace S)]
    {U U' : Over B} {P : AlgebraicGeometry.AlgebraicSpace.PreRelation U},
    P.IsPreEquivalence → (g : U' ⟶ U) → (P.pullback g).IsPreEquivalence)

#check (@AlgebraicGeometry.AlgebraicSpace.PreRelation.instIsEquivalenceRelationPullback :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
    [CategoryTheory.Limits.HasPullbacks (AlgebraicGeometry.AlgebraicSpace S)]
    {U U' : Over B} (P : AlgebraicGeometry.AlgebraicSpace.PreRelation U)
    (g : U' ⟶ U) [IsEquivalenceRelation P.t P.s],
    IsEquivalenceRelation (P.pullback g).t (P.pullback g).s)
