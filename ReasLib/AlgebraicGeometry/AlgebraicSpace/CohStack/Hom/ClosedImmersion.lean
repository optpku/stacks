module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Representable

/-!
# Closed immersions of lifted groupoid fibrations
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupScheme
open FiberedCategoryOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack.Hom

/-- A 1-morphism of lifted groupoid fibrations over `Over S` is a closed
immersion when it is representable by algebraic spaces and every representing
morphism `fy : Fy ⟶ ofOver U` is a closed immersion of algebraic spaces. -/
class ClosedImmersion {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) : Prop where
  /-- The 1-morphism is representable by algebraic spaces. -/
  representable : Classifying.relativelyRepresentableByAlgebraicSpaces f
  /-- Every representing morphism of algebraic spaces is a closed immersion. -/
  of_represents : ∀ ⦃U : Over S⦄ (y : Classifying.slice U ⟶ Y)
    (Fy : AlgebraicSpace S) (fy : Fy ⟶ AlgebraicSpace.ofOver U),
    Classifying.RepresentsBaseChange f y Fy fy → AlgebraicSpace.IsClosedImmersion fy

namespace ClosedImmersion

/-- The identity 1-morphism of a category fibred in groupoids is a closed
immersion. -/
instance id {S : Scheme.{u}}
    {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)} :
    ClosedImmersion (𝟙 X) := sorry

/-- A representing morphism of algebraic spaces for a closed immersion of
groupoid fibrations is a closed immersion. -/
theorem spec {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) [ClosedImmersion f] {U : Over S} (y : Classifying.slice U ⟶ Y)
    {Fy : AlgebraicSpace S} {fy : Fy ⟶ AlgebraicSpace.ofOver U}
    (h : Classifying.RepresentsBaseChange f y Fy fy) :
    AlgebraicSpace.IsClosedImmersion fy := sorry

/-- A closed immersion of groupoid fibrations is representable by algebraic
spaces. -/
theorem relativelyRepresentable {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) [ClosedImmersion f] :
    Classifying.relativelyRepresentableByAlgebraicSpaces f := sorry

/-- A 1-morphism is a closed immersion if and only if it is representable by
algebraic spaces and every representing morphism of algebraic spaces is a
closed immersion. -/
theorem iff {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) :
    ClosedImmersion f ↔
      Classifying.relativelyRepresentableByAlgebraicSpaces f ∧
        ∀ ⦃U : Over S⦄ (y : Classifying.slice U ⟶ Y) (Fy : AlgebraicSpace S)
          (fy : Fy ⟶ AlgebraicSpace.ofOver U),
          Classifying.RepresentsBaseChange f y Fy fy →
            AlgebraicSpace.IsClosedImmersion fy := sorry

end ClosedImmersion

end AlgebraicGeometry.AlgebraicSpace.CohStack.Hom
