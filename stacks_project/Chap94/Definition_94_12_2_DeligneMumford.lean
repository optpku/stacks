/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

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

/-- A Deligne-Mumford stack over a scheme `S` is an algebraic stack over `S`
that admits a scheme atlas which is surjective and étale. -/
class DeligneMumfordStack {S : Scheme.{u}} (X : GroupoidsOver S) : Prop
    extends AlgebraicStack X where
  /-- There is a scheme `U` over `S` and a surjective étale 1-morphism
  `GroupoidsOver.slice U ⟶ X`. -/
  existsEtaleSurjectiveAtlas :
    ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
      Groupoids.Hom.Etale p ∧ Groupoids.Hom.Surjective p

namespace DeligneMumfordStack

/-- The canonical slice fibration of a scheme over `S` is a Deligne-Mumford
stack. -/
instance slice {S : Scheme.{u}} (U : Over S) :
    DeligneMumfordStack (GroupoidsOver.slice U) := sorry

/-- The groupoid fibration of an algebraic space is a Deligne-Mumford stack. -/
instance ofAlgebraicSpace {S : Scheme.{u}} (F : AlgebraicSpace S) :
    DeligneMumfordStack F.toGroupoids := sorry

/-- An algebraic stack with a surjective étale scheme atlas is a
Deligne-Mumford stack. -/
theorem of_etale_atlas {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    (h : ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
      Groupoids.Hom.Etale p ∧ Groupoids.Hom.Surjective p) :
    DeligneMumfordStack X := sorry

/-- Being a Deligne-Mumford stack is equivalent to being an algebraic stack
that admits a surjective étale scheme atlas. -/
theorem iff {S : Scheme.{u}} (X : GroupoidsOver S) :
    DeligneMumfordStack X ↔
      AlgebraicStack X ∧
        ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
          Groupoids.Hom.Etale p ∧ Groupoids.Hom.Surjective p := sorry

/-- A Deligne-Mumford stack admits a surjective étale scheme atlas. -/
theorem exists_etale_surjective_atlas {S : Scheme.{u}} (X : GroupoidsOver S)
    [DeligneMumfordStack X] :
    ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
      Groupoids.Hom.Etale p ∧ Groupoids.Hom.Surjective p := sorry

/-- The object property on categories fibred in groupoids over `Over S`
selecting Deligne-Mumford stacks. -/
def objectProperty (S : Scheme.{u}) : ObjectProperty (GroupoidsOver S) :=
  fun X ↦ DeligneMumfordStack X

/-- The object property of Deligne-Mumford stacks is the class
`DeligneMumfordStack`. -/
theorem objectProperty_apply {S : Scheme.{u}} (X : GroupoidsOver S) :
    objectProperty S X ↔ DeligneMumfordStack X := sorry

/-- Equivalently, the atlas in the definition of a Deligne-Mumford stack may be
taken to be a representable category fibred in groupoids, i.e. one equivalent
to a canonical slice. -/
theorem iff_exists_representable_atlas {S : Scheme.{u}} (X : GroupoidsOver S) :
    DeligneMumfordStack X ↔
      AlgebraicStack X ∧
        ∃ (U : GroupoidsOver S) (p : U ⟶ X),
          FiberedCategoryOver.Groupoids.IsRepresentable U ∧
            Groupoids.Hom.Etale p ∧ Groupoids.Hom.Surjective p := sorry

end DeligneMumfordStack

end AlgebraicGeometry
