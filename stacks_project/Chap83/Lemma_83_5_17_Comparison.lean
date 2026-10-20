/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.Comparison
public import stacks_project.Chap83.Definition_83_4_1_Invariant

/-!
# Comparison square of a pre-relation and a morphism

The canonical comparison morphism, its pullback projections, and the induced
kernel-pair morphism are available from their shared mathematical owner.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits
open AlgebraicGeometry.AlgebraicSpace.PreRelation

universe u

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.comparison :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B} (φ : U ⟶ X),
      pullback φ φ ⟶ U ⨯ U)

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.comparison_fst :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (φ : U ⟶ X),
      comparison φ ≫ prod.fst = pullback.fst φ φ)

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.comparison_snd :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (φ : U ⟶ X),
      comparison φ ≫ prod.snd = pullback.snd φ φ)

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.comparison_spec :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (φ : U ⟶ X),
      comparison φ ≫ prod.fst = pullback.fst φ φ ∧
      comparison φ ≫ prod.snd = pullback.snd φ φ)

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.toRelation :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X),
      pullback (comparison φ) P.hom ⟶ P.left)

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.toRelation_spec :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X),
      P.toRelation φ = pullback.snd (comparison φ) P.hom)

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.toKernelPair :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X),
      pullback (comparison φ) P.hom ⟶ pullback φ φ)

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.toKernelPair_spec :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X),
      P.toKernelPair φ = pullback.fst (comparison φ) P.hom)

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.toKernelPair_comp_comparison :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X : Over B} (P : PreRelation U) (φ : U ⟶ X),
      P.toKernelPair φ ≫ comparison φ = P.toRelation φ ≫ P.hom)

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.induced :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariant φ),
      P.left ⟶ pullback φ φ)

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.induced_fst :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariant φ),
      P.induced hφ ≫ pullback.fst φ φ = P.t)

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.induced_snd :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariant φ),
      P.induced hφ ≫ pullback.snd φ φ = P.s)

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.induced_comp :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariant φ),
      P.induced hφ ≫ comparison φ = P.hom)
