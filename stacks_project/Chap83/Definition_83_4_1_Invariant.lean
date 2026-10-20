/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap83.Lemma_83_3_2_Invariant

/-!
# Invariant morphisms of a pre-relation

A morphism out of the underlying space of a pre-relation is `R`-invariant when it
equalizes the two projections. This is the existing morphism-level predicate
`IsInvariantHom`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace PreRelation

/-- A morphism `φ : U ⟶ X` over `B` is `R`-invariant for a pre-relation `P` when it
equalizes the two projections `P.t` and `P.s`. -/
abbrev IsInvariant {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) : Prop :=
  P.IsInvariantHom φ

/-- `R`-invariance is the equality `P.t ≫ φ = P.s ≫ φ`. -/
theorem isInvariant_iff {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) :
    P.IsInvariant φ ↔ P.t ≫ φ = P.s ≫ φ :=
  Iff.rfl

/-- `IsInvariant` is the existing morphism-level predicate `IsInvariantHom`. -/
theorem isInvariant_iff_isInvariantHom {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X : Over B} (P : PreRelation U) (φ : U ⟶ X) :
    P.IsInvariant φ ↔ P.IsInvariantHom φ :=
  Iff.rfl

end PreRelation
end AlgebraicGeometry.AlgebraicSpace
