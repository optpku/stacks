module

public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap101.Lemma_101_17_5_LocallyOfFiniteType
public import stacks_project.Chap106.Theorem_106_13_9_Keel_Mori

/-!
# Locally of finite type for Keel–Mori moduli spaces

If an algebraic stack of finite inertia maps locally of finite type to a
locally Noetherian algebraic space, then a uniform categorical moduli space
induces a locally-of-finite-type morphism of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids.Inertia
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 106.14.1. Let `p : X ⟶ Y.toGroupoids` be a morphism from an algebraic
stack to an algebraic space. Assume the inertia morphism `forget X : I_X ⟶ X`
is finite, the algebraic space `Y` is locally Noetherian, and `p` is locally of
finite type. Let `f : X ⟶ M.toGroupoids` be a uniform categorical moduli space
as constructed in Theorem 106.13.9, and let `q : M ⟶ Y` be the induced
morphism with 2-cell `α : f ≫ AlgebraicSpace.toGroupoids.map q ≅ p`. Then `q`
is locally of finite type. -/
@[stacks 0DUX]
theorem locallyOfFiniteType_of_isUniformCategoricalModuliSpace
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {Y M : AlgebraicSpace S} [IsFinite (forget.{u + 1, u, u, u + 1} X)]
    [AlgebraicSpace.IsLocallyNoetherian Y] (p : X ⟶ Y.toGroupoids)
    [AlgebraicStack.LocallyOfFiniteType p] (f : X ⟶ M.toGroupoids)
    [IsUniformCategoricalModuliSpace f] (q : M ⟶ Y)
    (α : f ≫ AlgebraicSpace.toGroupoids.map q ≅ p) :
    AlgebraicSpace.LocallyOfFiniteType q :=
  sorry

end AlgebraicGeometry.AlgebraicStack
