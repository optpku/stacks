/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Invariant morphisms of a pre-relation

A morphism of algebraic spaces over a base is invariant under a pre-relation when it
equalizes the source and target projections.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

/-- A morphism `φ : U ⟶ X` of algebraic spaces over `B` is invariant under a pre-relation
`P` when it equalizes the source and target projections of `P`.

This is the morphism-level predicate (equalizing `P.t` and `P.s`). It is distinct from
`IsInvariant` on subobjects of `U`.
-/
def IsInvariantHom {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) : Prop :=
  P.t ≫ φ = P.s ≫ φ

/-- Invariance of a morphism over `B` is equalization of the two projections. -/
theorem isInvariantHom_iff {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) :
    P.IsInvariantHom φ ↔ P.t ≫ φ = P.s ≫ φ :=
  sorry

/-- Invariance of a morphism over `B` is equivalent to equalization of the underlying
morphisms of algebraic spaces over `S`. -/
theorem isInvariantHom_left {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) :
    P.IsInvariantHom φ ↔ P.t.left ≫ φ.left = P.s.left ≫ φ.left :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.PreRelation
