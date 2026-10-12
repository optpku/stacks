/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap108.Lemma_108_4_2_QuasiSeparated

/-!
# Separated morphisms of CohStack-sized groupoid fibrations

A 1-morphism in `FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)`
is separated when its relative 2-diagonal is representable by algebraic spaces
and proper, matching Definition 101.4.1 at the Hom-universe of
`CohStack.toGroupoids`.
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
Hom-universe of `CohStack.toGroupoids`, is separated when its relative
2-diagonal is representable by algebraic spaces and proper on scheme-slice
representing morphisms. -/
class Separated {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) : Prop where
  /-- The relative 2-diagonal is representable by algebraic spaces. -/
  representable_diagonal :
    Classifying.relativelyRepresentableByAlgebraicSpaces (diagonal f)
  /-- The relative 2-diagonal is proper. -/
  proper_diagonal : has (@AlgebraicSpace.Proper S) (diagonal f)

namespace Separated

/-- The identity 1-morphism of a category fibred in groupoids is separated. -/
instance id {S : Scheme.{u}}
    {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)} :
    Separated (𝟙 X) :=
  sorry

/-- A 1-morphism is separated if and only if its relative 2-diagonal is
representable by algebraic spaces and proper. -/
theorem iff {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) :
    Separated f ↔
      Classifying.relativelyRepresentableByAlgebraicSpaces (diagonal f) ∧
        has (@AlgebraicSpace.Proper S) (diagonal f) :=
  sorry

/-- The relative 2-diagonal of a separated 1-morphism is representable by
algebraic spaces and proper. -/
theorem spec {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) [Separated f] :
    Classifying.relativelyRepresentableByAlgebraicSpaces (diagonal f) ∧
      has (@AlgebraicSpace.Proper S) (diagonal f) :=
  sorry

end Separated

end AlgebraicGeometry.AlgebraicSpace.CohStack.Hom
