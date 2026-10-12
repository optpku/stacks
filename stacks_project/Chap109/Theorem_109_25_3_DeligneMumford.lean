/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import stacks_project.Chap108.Lemma_108_4_2_QuasiSeparated
public import stacks_project.Chap108.Lemma_108_4_8_Algebraic

/-!
# Deligne–Mumford stacks in the Hom-universe of `CohStack.toGroupoids`

A Deligne–Mumford stack in `FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)`
is an algebraic stack that admits a scheme atlas which is representable by algebraic
spaces, étale, and surjective, matching Definition 94.12.2 at the Hom-universe of
`CohStack.toGroupoids`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupScheme
open FiberedCategoryOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

/-- A Deligne–Mumford stack over a scheme `S`, in the Hom-universe of
`CohStack.toGroupoids`, is an algebraic stack over `S` that admits a scheme
atlas which is representable by algebraic spaces, étale, and surjective. -/
class DeligneMumfordStack {S : Scheme.{u}}
    (X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)) : Prop
    extends AlgebraicStack X where
  /-- There is a scheme `U` over `S` and a representable étale surjective
  1-morphism `Classifying.slice U ⟶ X`. -/
  existsEtaleSurjectiveAtlas :
    ∃ (U : Over S) (p : Classifying.slice U ⟶ X),
      Classifying.relativelyRepresentableByAlgebraicSpaces p ∧
        Hom.has (@AlgebraicSpace.Etale S) p ∧ Classifying.Surjective p

namespace DeligneMumfordStack

/-- The canonical slice fibration of a scheme over `S` is a Deligne–Mumford
stack. -/
instance slice {S : Scheme.{u}} (U : Over S) :
    DeligneMumfordStack (Classifying.slice U) :=
  sorry

/-- The groupoid fibration of an algebraic space is a Deligne–Mumford stack. -/
instance ofAlgebraicSpace {S : Scheme.{u}} (F : AlgebraicSpace S) :
    DeligneMumfordStack (Classifying.toGroupoids F) :=
  sorry

/-- An algebraic stack with a representable étale surjective scheme atlas is a
Deligne–Mumford stack. -/
theorem of_etale_atlas {S : Scheme.{u}}
    (X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S))
    [AlgebraicStack X]
    (h : ∃ (U : Over S) (p : Classifying.slice U ⟶ X),
      Classifying.relativelyRepresentableByAlgebraicSpaces p ∧
        Hom.has (@AlgebraicSpace.Etale S) p ∧ Classifying.Surjective p) :
    DeligneMumfordStack X :=
  sorry

/-- Being a Deligne–Mumford stack is equivalent to being an algebraic stack
that admits a representable étale surjective scheme atlas. -/
theorem iff {S : Scheme.{u}}
    (X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)) :
    DeligneMumfordStack X ↔
      AlgebraicStack X ∧
        ∃ (U : Over S) (p : Classifying.slice U ⟶ X),
          Classifying.relativelyRepresentableByAlgebraicSpaces p ∧
            Hom.has (@AlgebraicSpace.Etale S) p ∧ Classifying.Surjective p :=
  sorry

/-- A Deligne–Mumford stack admits a representable étale surjective scheme
atlas. -/
theorem exists_etale_surjective_atlas {S : Scheme.{u}}
    (X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S))
    [DeligneMumfordStack X] :
    ∃ (U : Over S) (p : Classifying.slice U ⟶ X),
      Classifying.relativelyRepresentableByAlgebraicSpaces p ∧
        Hom.has (@AlgebraicSpace.Etale S) p ∧ Classifying.Surjective p :=
  sorry

/-- The defining clauses of a Deligne–Mumford stack: an algebraic stack together
with a representable étale surjective scheme atlas. -/
theorem spec {S : Scheme.{u}}
    (X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S))
    [DeligneMumfordStack X] :
    AlgebraicStack X ∧
      ∃ (U : Over S) (p : Classifying.slice U ⟶ X),
        Classifying.relativelyRepresentableByAlgebraicSpaces p ∧
          Hom.has (@AlgebraicSpace.Etale S) p ∧ Classifying.Surjective p :=
  sorry

end DeligneMumfordStack

end AlgebraicGeometry.AlgebraicSpace.CohStack
