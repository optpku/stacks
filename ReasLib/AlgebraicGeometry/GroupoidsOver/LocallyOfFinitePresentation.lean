module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.GroupoidsOver.MorphismProperty

/-!
# Locally of finite presentation morphisms of groupoid fibrations

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` that is
representable by algebraic spaces is locally of finite presentation when every
representing morphism of algebraic spaces `Fy ⟶ ofOver U` is locally of finite
presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- A 1-morphism of categories fibred in groupoids over `Over S` is locally of
finite presentation when it is representable by algebraic spaces and every
representing morphism `fy : Fy ⟶ ofOver U` is a locally of finite presentation
morphism of algebraic spaces. -/
class LocallyOfFinitePresentation {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) : Prop where
  /-- The 1-morphism is representable by algebraic spaces. -/
  representable : relativelyRepresentableByAlgebraicSpaces f
  /-- Every representing morphism of algebraic spaces is locally of finite
  presentation. -/
  of_represents : ∀ ⦃U : Over S⦄ (y : GroupoidsOver.slice U ⟶ Y)
    (Fy : AlgebraicSpace S) (fy : Fy ⟶ AlgebraicSpace.ofOver U),
    RepresentsBaseChange f y Fy fy → AlgebraicSpace.LocallyOfFinitePresentation fy

namespace LocallyOfFinitePresentation

/-- The identity 1-morphism of a category fibred in groupoids is locally of
finite presentation. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} :
    LocallyOfFinitePresentation (𝟙 X) :=
  sorry

/-- A representing morphism of algebraic spaces for a locally of finite
presentation 1-morphism is locally of finite presentation. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] {U : Over S} (y : GroupoidsOver.slice U ⟶ Y)
    {Fy : AlgebraicSpace S} {fy : Fy ⟶ AlgebraicSpace.ofOver U}
    (h : RepresentsBaseChange f y Fy fy) :
    AlgebraicSpace.LocallyOfFinitePresentation fy :=
  sorry

/-- A locally of finite presentation 1-morphism is representable by algebraic
spaces. -/
theorem relativelyRepresentable {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) [LocallyOfFinitePresentation f] :
    relativelyRepresentableByAlgebraicSpaces f :=
  sorry

/-- A 1-morphism is locally of finite presentation if and only if it is
representable by algebraic spaces and every representing morphism of algebraic
spaces is locally of finite presentation. -/
theorem iff {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    LocallyOfFinitePresentation f ↔ relativelyRepresentableByAlgebraicSpaces f ∧
      ∀ ⦃U : Over S⦄ (y : GroupoidsOver.slice U ⟶ Y) (Fy : AlgebraicSpace S)
        (fy : Fy ⟶ AlgebraicSpace.ofOver U),
        RepresentsBaseChange f y Fy fy →
          AlgebraicSpace.LocallyOfFinitePresentation fy :=
  sorry

end LocallyOfFinitePresentation

end AlgebraicGeometry.Groupoids.Hom
