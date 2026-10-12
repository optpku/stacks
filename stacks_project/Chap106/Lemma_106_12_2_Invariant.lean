/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.PreRelation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.Invariant
public import stacks_project.Chap94.Definition_94_16_5_Quotient
public import stacks_project.Chap94.«94_8_2_1_FullyFaithful»

/-!
# Invariant morphisms out of a groupoid in algebraic spaces

A morphism from the object space of a groupoid in algebraic spaces to an
algebraic space is `R`-invariant when it equalizes source and target. The
atlas composite recovers such a morphism from a map out of the quotient stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- A morphism `φ : U ⟶ Y` of algebraic spaces over `S` is `R`-invariant for a
groupoid `G` in algebraic spaces when it equalizes the source and target maps
of `G`. -/
def IsInvariantHom {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {Y : AlgebraicSpace S}
    (φ : G.U.left ⟶ Y) : Prop :=
  G.t.left ≫ φ = G.s.left ≫ φ

/-- `R`-invariance of a morphism of algebraic spaces over `S` is equalization of
the source and target maps. -/
theorem isInvariantHom_iff {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {Y : AlgebraicSpace S}
    (φ : G.U.left ⟶ Y) :
    G.IsInvariantHom φ ↔ G.t.left ≫ φ = G.s.left ≫ φ :=
  sorry

/-- Left-level `R`-invariance of a morphism over `B` agrees with invariance for
the underlying pre-relation. -/
theorem isInvariantHom_iff_toPreRelation {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X : Over B} (ψ : G.U ⟶ X) :
    G.IsInvariantHom ψ.left ↔ G.toPreRelation.IsInvariantHom ψ :=
  sorry

/-- The composite `U ⟶ [U / R] ⟶ Y` recovered from a morphism of the quotient
stack to an algebraic space. -/
def atlasComp {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {Y : AlgebraicSpace S}
    (f : G.quotientStack ⟶ Y.toGroupoids) : G.U.left ⟶ Y :=
  AlgebraicSpace.toGroupoids.eval (G.atlas ≫ f)

/-- `atlasComp f` is evaluation of the composite of the atlas with `f`. -/
theorem atlasComp_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {Y : AlgebraicSpace S}
    (f : G.quotientStack ⟶ Y.toGroupoids) :
    G.atlasComp f = AlgebraicSpace.toGroupoids.eval (G.atlas ≫ f) :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
