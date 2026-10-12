/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty

/-!
# Affine morphisms of groupoid fibrations

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` that is
representable by algebraic spaces is affine when every representing morphism
of algebraic spaces `fy : Fy ⟶ ofOver U` is an affine morphism of algebraic
spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- A 1-morphism of categories fibred in groupoids over `Over S` is affine when
it is representable by algebraic spaces and every representing morphism
`fy : Fy ⟶ ofOver U` is an affine morphism of algebraic spaces. -/
class Affine {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) : Prop where
  /-- The 1-morphism is representable by algebraic spaces. -/
  representable : relativelyRepresentableByAlgebraicSpaces f
  /-- Every representing morphism of algebraic spaces is affine. -/
  of_represents : ∀ ⦃U : Over S⦄ (y : GroupoidsOver.slice U ⟶ Y)
    (Fy : AlgebraicSpace S) (fy : Fy ⟶ AlgebraicSpace.ofOver U),
    RepresentsBaseChange f y Fy fy → AlgebraicSpace.Affine fy

namespace Affine

/-- The identity 1-morphism of a category fibred in groupoids is affine. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} : Affine (𝟙 X) := sorry

/-- A representing morphism of algebraic spaces for an affine 1-morphism is
affine. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) [Affine f]
    {U : Over S} (y : GroupoidsOver.slice U ⟶ Y) {Fy : AlgebraicSpace S}
    {fy : Fy ⟶ AlgebraicSpace.ofOver U} (h : RepresentsBaseChange f y Fy fy) :
    AlgebraicSpace.Affine fy := sorry

/-- An affine 1-morphism is representable by algebraic spaces. -/
theorem relativelyRepresentable {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) [Affine f] : relativelyRepresentableByAlgebraicSpaces f := sorry

/-- A 1-morphism is affine if and only if it is representable by algebraic
spaces and has the algebraic-space affine property in the sense of
scheme-slice tests. -/
theorem iff {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    Affine f ↔ relativelyRepresentableByAlgebraicSpaces f ∧
      has (@AlgebraicSpace.Affine S) f := sorry

/-- An affine 1-morphism has the algebraic-space affine property on
scheme-slice representing morphisms. -/
theorem has_affine {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    [Affine f] : has (@AlgebraicSpace.Affine S) f := sorry

/-- An affine morphism of algebraic spaces induces an affine 1-morphism of the
associated groupoid fibrations. -/
instance of_toGroupoids {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [AlgebraicSpace.Affine f] : Affine (AlgebraicSpace.toGroupoids.map f) :=
  sorry

end Affine

end AlgebraicGeometry.Groupoids.Hom
