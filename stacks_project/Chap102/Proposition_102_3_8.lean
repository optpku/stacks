module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap102.Definition_102_3_1_LimitPreserving
public import stacks_project.Chap106.Lemma_106_10_1_LocallyOfFinitePresentation

/-!
# Morphisms of algebraic stacks locally of finite presentation

A morphism of algebraic stacks is limit preserving if and only if it is
limit preserving on objects, if and only if it is locally of finite
presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation

/-- Proposition 102.3.8: Let `f : 𝒳 ⟶ 𝒴` be a morphism of algebraic stacks.
The following are equivalent: `f` is limit preserving, `f` is limit
preserving on objects, and `f` is locally of finite presentation. -/
@[stacks 0CMY]
theorem tfae {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    List.TFAE [Groupoids.Hom.LimitPreserving f,
      Groupoids.Hom.LimitPreservingOnObjects f,
      AlgebraicStack.LocallyOfFinitePresentation f] := sorry

/-- A morphism of algebraic stacks is limit preserving if and only if it is
limit preserving on objects. -/
theorem iff_limitPreservingOnObjects {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    Groupoids.Hom.LimitPreserving f ↔
      Groupoids.Hom.LimitPreservingOnObjects f := sorry

/-- A morphism of algebraic stacks is limit preserving if and only if it is
locally of finite presentation. -/
theorem iff_locallyOfFinitePresentation {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    Groupoids.Hom.LimitPreserving f ↔
      AlgebraicStack.LocallyOfFinitePresentation f := sorry

/-- A morphism of algebraic stacks that is limit preserving on objects is
locally of finite presentation. -/
theorem of_limitPreservingOnObjects {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [Groupoids.Hom.LimitPreservingOnObjects f] :
    AlgebraicStack.LocallyOfFinitePresentation f := sorry

/-- A morphism of algebraic stacks that is locally of finite presentation is
limit preserving as a 1-morphism of categories fibred in groupoids. -/
instance homLimitPreserving {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.LocallyOfFinitePresentation f] :
    Groupoids.Hom.LimitPreserving f := sorry

end AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation
