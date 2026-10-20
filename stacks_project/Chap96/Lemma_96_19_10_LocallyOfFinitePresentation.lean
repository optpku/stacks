module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.LocallyOfFinitePresentation

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

/- A 1-morphism of categories fibred in groupoids over `Over S` is locally of
finite presentation when it is representable by algebraic spaces and every
representing morphism `fy : Fy ⟶ ofOver U` is a locally of finite presentation
morphism of algebraic spaces. -/
#check (AlgebraicGeometry.Groupoids.Hom.LocallyOfFinitePresentation :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}, (X ⟶ Y) → Prop)

namespace LocallyOfFinitePresentation

/- The identity 1-morphism of a category fibred in groupoids is locally of
finite presentation. -/
#check (AlgebraicGeometry.Groupoids.Hom.LocallyOfFinitePresentation.id :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S},
    LocallyOfFinitePresentation (𝟙 X))

/- A representing morphism of algebraic spaces for a locally of finite
presentation 1-morphism is locally of finite presentation. -/
#check (AlgebraicGeometry.Groupoids.Hom.LocallyOfFinitePresentation.spec :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] {U : Over S} (y : GroupoidsOver.slice U ⟶ Y)
    {Fy : AlgebraicSpace S} {fy : Fy ⟶ AlgebraicSpace.ofOver U},
    RepresentsBaseChange f y Fy fy → AlgebraicSpace.LocallyOfFinitePresentation fy)

/- A locally of finite presentation 1-morphism is representable by algebraic
spaces. -/
#check (AlgebraicGeometry.Groupoids.Hom.LocallyOfFinitePresentation.relativelyRepresentable :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) [LocallyOfFinitePresentation f],
    relativelyRepresentableByAlgebraicSpaces f)

/- A 1-morphism is locally of finite presentation if and only if it is
representable by algebraic spaces and every representing morphism of algebraic
spaces is locally of finite presentation. -/
#check (AlgebraicGeometry.Groupoids.Hom.LocallyOfFinitePresentation.iff :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y),
    LocallyOfFinitePresentation f ↔ relativelyRepresentableByAlgebraicSpaces f ∧
      ∀ ⦃U : Over S⦄ (y : GroupoidsOver.slice U ⟶ Y) (Fy : AlgebraicSpace S)
        (fy : Fy ⟶ AlgebraicSpace.ofOver U),
        RepresentsBaseChange f y Fy fy →
          AlgebraicSpace.LocallyOfFinitePresentation fy)

end LocallyOfFinitePresentation

end AlgebraicGeometry.Groupoids.Hom
