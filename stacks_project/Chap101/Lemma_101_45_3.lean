module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import stacks_project.Chap101.Lemma_101_36_4_Unramified
public import stacks_project.Chap101.Lemma_101_45_5_Comparison
public import stacks_project.Chap101.Remark_101_19_5_AutomorphismGroup

/-!
# Unramified morphisms and automorphism groups

For an unramified morphism of algebraic stacks, the inertia comparison
`I_X ⟶ X ×_Y I_Y` is an isomorphism if and only if the morphism induces an
isomorphism of automorphism groups at every point of `|X|`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Inertia

/-- Lemma 101.45.3: let `f : X ⟶ Y` be an unramified morphism of algebraic
stacks. The canonical 1-morphism `comparison f : I_X ⟶ X ×_Y I_Y` is an
isomorphism of stacks if and only if `f` induces an isomorphism between
automorphism groups at `x` and `f(x)` (Remark 101.19.5) for every
`x ∈ |X|`. -/
@[stacks 0DU9]
theorem comparison_isEquivalence_iff_forall_isIsoAt {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [Unramified f] :
    (toBasedFunctor (comparison f)).IsEquivalence ↔
      ∀ x : |X|, automorphismGroup.IsIsoAt f x :=
  sorry

/-- If the inertia comparison of an unramified morphism is an isomorphism of
stacks, then the morphism induces an isomorphism of automorphism groups at
every point of `|X|`. -/
theorem forall_isIsoAt_of_comparison_isEquivalence {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [Unramified f] :
    (toBasedFunctor (comparison f)).IsEquivalence →
      ∀ x : |X|, automorphismGroup.IsIsoAt f x :=
  sorry

/-- If an unramified morphism induces an isomorphism of automorphism groups at
every point of `|X|`, then the inertia comparison is an isomorphism of
stacks. -/
theorem comparison_isEquivalence_of_forall_isIsoAt {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [Unramified f] :
    (∀ x : |X|, automorphismGroup.IsIsoAt f x) →
      (toBasedFunctor (comparison f)).IsEquivalence :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Inertia
