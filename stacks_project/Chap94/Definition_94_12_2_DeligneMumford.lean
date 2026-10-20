module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.DeligneMumford
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap94.Definition_94_12_2_Etale

/-!
# Deligne-Mumford stacks over a scheme

A Deligne-Mumford stack over a scheme `S` is an algebraic stack over `S` that
admits a scheme atlas which is surjective and étale.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

#check (AlgebraicGeometry.DeligneMumfordStack :
  ∀ {S : Scheme.{u}}, GroupoidsOver S → Prop)

namespace DeligneMumfordStack

#check (AlgebraicGeometry.DeligneMumfordStack.slice :
  ∀ {S : Scheme.{u}} (U : Over S),
    DeligneMumfordStack (GroupoidsOver.slice U))

#check (AlgebraicGeometry.DeligneMumfordStack.ofAlgebraicSpace :
  ∀ {S : Scheme.{u}} (F : AlgebraicSpace S),
    DeligneMumfordStack F.toGroupoids)

#check (AlgebraicGeometry.DeligneMumfordStack.of_etale_atlas :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    (h : ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
      Groupoids.Hom.Etale p ∧ Groupoids.Hom.Surjective p),
    DeligneMumfordStack X)

#check (AlgebraicGeometry.DeligneMumfordStack.iff :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    DeligneMumfordStack X ↔
      AlgebraicStack X ∧
        ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
          Groupoids.Hom.Etale p ∧ Groupoids.Hom.Surjective p)

#check (AlgebraicGeometry.DeligneMumfordStack.exists_etale_surjective_atlas :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    [DeligneMumfordStack X],
    ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
      Groupoids.Hom.Etale p ∧ Groupoids.Hom.Surjective p)

#check (AlgebraicGeometry.DeligneMumfordStack.objectProperty :
  ∀ (S : Scheme.{u}),
    ObjectProperty (GroupoidsOver S))

#check (AlgebraicGeometry.DeligneMumfordStack.objectProperty_apply :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    objectProperty S X ↔ DeligneMumfordStack X)

#check (AlgebraicGeometry.DeligneMumfordStack.iff_exists_representable_atlas :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    DeligneMumfordStack X ↔
      AlgebraicStack X ∧
        ∃ (U : GroupoidsOver S) (p : U ⟶ X),
          FiberedCategoryOver.Groupoids.IsRepresentable U ∧
            Groupoids.Hom.Etale p ∧ Groupoids.Hom.Surjective p)

end DeligneMumfordStack

end AlgebraicGeometry
