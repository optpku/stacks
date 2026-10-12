/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import stacks_project.Chap101.Lemma_101_17_5_LocallyOfFiniteType
public import stacks_project.Chap101.Lemma_101_36_4_Etale
public import stacks_project.Chap101.Lemma_101_36_4_Unramified
public import stacks_project.Chap94.Lemma_94_14_3_Pullback

/-!
# Diagonal criterion for unramified morphisms of algebraic stacks

A morphism of algebraic stacks is unramified if and only if it is locally of
finite type and its relative 2-diagonal is étale.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Unramified

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y]

/-- Lemma 101.36.9: a morphism `f : X ⟶ Y` of algebraic stacks is unramified
if and only if it is locally of finite type and its relative 2-diagonal
`Hom.diagonal f : X ⟶ X ×_Y X` is étale. -/
@[stacks 0CJ0]
theorem iff_locallyOfFiniteType_and_etale_diagonal (f : X ⟶ Y) :
    Unramified f ↔
      LocallyOfFiniteType f ∧ Etale (Hom.diagonal.{u + 1, u, u + 1} f) :=
  sorry

/-- An unramified morphism of algebraic stacks is locally of finite type. -/
@[stacks 0CJ0]
instance locallyOfFiniteType (f : X ⟶ Y) [Unramified f] :
    LocallyOfFiniteType f :=
  sorry

/-- The relative 2-diagonal of an unramified morphism of algebraic stacks is
étale. -/
@[stacks 0CJ0]
instance etale_diagonal (f : X ⟶ Y) [Unramified f] :
    Etale (Hom.diagonal.{u + 1, u, u + 1} f) :=
  sorry

/-- A locally of finite type morphism of algebraic stacks whose relative
2-diagonal is étale is unramified. -/
@[stacks 0CJ0, instance 900]
instance of_etale_diagonal (f : X ⟶ Y)
    [LocallyOfFiniteType f] [Etale (Hom.diagonal.{u + 1, u, u + 1} f)] :
    Unramified f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Unramified
