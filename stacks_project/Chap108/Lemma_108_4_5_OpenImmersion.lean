/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap110.Lemma_110_53_1

/-!
# Open immersions of CohStack-sized groupoid fibrations

A 1-morphism in `FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)`
is an open immersion when it is representable by algebraic spaces and every
representing morphism `fy : Fy ⟶ ofOver U` is an open immersion of algebraic
spaces, matching Definition 100.9.1 at the Hom-universe of `CohStack.toGroupoids`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupScheme
open FiberedCategoryOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack.Hom

/-- A 1-morphism of categories fibred in groupoids over `Over S`, in the
Hom-universe of `CohStack.toGroupoids`, is an open immersion when it is
representable by algebraic spaces and every representing morphism
`fy : Fy ⟶ ofOver U` is an open immersion of algebraic spaces. -/
class OpenImmersion {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) : Prop where
  /-- The 1-morphism is representable by algebraic spaces. -/
  representable : Classifying.relativelyRepresentableByAlgebraicSpaces f
  /-- Every representing morphism of algebraic spaces is an open immersion. -/
  of_represents : ∀ ⦃U : Over S⦄ (y : Classifying.slice U ⟶ Y)
    (Fy : AlgebraicSpace S) (fy : Fy ⟶ AlgebraicSpace.ofOver U),
    Classifying.RepresentsBaseChange f y Fy fy → AlgebraicSpace.IsOpenImmersion fy

namespace OpenImmersion

/-- The identity 1-morphism of a category fibred in groupoids is an open
immersion. -/
instance id {S : Scheme.{u}}
    {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)} :
    OpenImmersion (𝟙 X) :=
  sorry

/-- A representing morphism of algebraic spaces for an open immersion of
groupoid fibrations is an open immersion. -/
theorem spec {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) [OpenImmersion f] {U : Over S} (y : Classifying.slice U ⟶ Y)
    {Fy : AlgebraicSpace S} {fy : Fy ⟶ AlgebraicSpace.ofOver U}
    (h : Classifying.RepresentsBaseChange f y Fy fy) :
    AlgebraicSpace.IsOpenImmersion fy :=
  sorry

/-- An open immersion of groupoid fibrations is representable by algebraic
spaces. -/
theorem relativelyRepresentable {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) [OpenImmersion f] :
    Classifying.relativelyRepresentableByAlgebraicSpaces f :=
  sorry

/-- A 1-morphism is an open immersion if and only if it is representable by
algebraic spaces and every representing morphism of algebraic spaces is an
open immersion. -/
theorem iff {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) :
    OpenImmersion f ↔
      Classifying.relativelyRepresentableByAlgebraicSpaces f ∧
        ∀ ⦃U : Over S⦄ (y : Classifying.slice U ⟶ Y) (Fy : AlgebraicSpace S)
          (fy : Fy ⟶ AlgebraicSpace.ofOver U),
          Classifying.RepresentsBaseChange f y Fy fy →
            AlgebraicSpace.IsOpenImmersion fy :=
  sorry

end OpenImmersion

end AlgebraicGeometry.AlgebraicSpace.CohStack.Hom
