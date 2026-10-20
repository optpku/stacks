/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.Invariant

/-!
# Invariant morphisms of a pre-relation

This chapter-facing module retains the established names for the canonical
invariant-morphism API.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.IsInvariantHom :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    {B : AlgebraicGeometry.AlgebraicSpace S}
    {U X : CategoryTheory.Over B},
    AlgebraicGeometry.AlgebraicSpace.PreRelation U →
      (U ⟶ X) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.isInvariantHom_iff :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    {B : AlgebraicGeometry.AlgebraicSpace S}
    {U X : CategoryTheory.Over B}
    (P : AlgebraicGeometry.AlgebraicSpace.PreRelation U) (φ : U ⟶ X),
    P.IsInvariantHom φ ↔ P.t ≫ φ = P.s ≫ φ)

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.isInvariantHom_left :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    {B : AlgebraicGeometry.AlgebraicSpace S}
    {U X : CategoryTheory.Over B}
    (P : AlgebraicGeometry.AlgebraicSpace.PreRelation U) (φ : U ⟶ X),
    P.IsInvariantHom φ ↔ P.t.left ≫ φ.left = P.s.left ≫ φ.left)
