module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import stacks_project.Chap100.Definition_100_5_1_Surjective
public import stacks_project.Chap101.Definition_101_10_1_Integral
public import stacks_project.Chap106.Lemma_106_10_1_LocallyOfFinitePresentation

/-!
# Well-nigh affine algebraic stacks

An algebraic stack is well-nigh affine when it admits a surjective, flat,
finite, and locally of finite presentation atlas from an affine scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- An algebraic stack is well-nigh affine if there exists an affine scheme `U`
and a 1-morphism `GroupoidsOver.slice U ⟶ X` that is surjective, flat, finite,
and locally of finite presentation. -/
@[mk_iff]
class IsWellNighAffine {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] : Prop where
  /-- There is a surjective, flat, finite, locally of finite presentation
  1-morphism from the slice of an affine scheme. -/
  exists_affine_atlas :
    ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
      IsAffine U.left ∧ AlgebraicStack.Surjective p ∧ AlgebraicStack.Flat p ∧
        AlgebraicStack.IsFinite p ∧ AlgebraicStack.LocallyOfFinitePresentation p

namespace IsWellNighAffine

/-- A well-nigh affine algebraic stack admits a surjective, flat, finite,
locally of finite presentation atlas from an affine scheme. -/
theorem spec {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsWellNighAffine X] :
    ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
      IsAffine U.left ∧ AlgebraicStack.Surjective p ∧ AlgebraicStack.Flat p ∧
        AlgebraicStack.IsFinite p ∧ AlgebraicStack.LocallyOfFinitePresentation p :=
  sorry

/-- A surjective, flat, finite, locally of finite presentation atlas from an
affine scheme witnesses that the algebraic stack is well-nigh affine. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] {U : Over S}
    [IsAffine U.left] (p : GroupoidsOver.slice U ⟶ X)
    [AlgebraicStack.Surjective p] [AlgebraicStack.Flat p]
    [AlgebraicStack.IsFinite p] [AlgebraicStack.LocallyOfFinitePresentation p] :
    IsWellNighAffine X :=
  sorry

end IsWellNighAffine

/-- The canonical slice of an affine scheme over `S` is a well-nigh affine
algebraic stack. -/
instance instIsWellNighAffine_slice {S : Scheme.{u}} (U : Over S)
    [IsAffine U.left] : IsWellNighAffine (GroupoidsOver.slice U) where
  exists_affine_atlas :=
    ⟨U, 𝟙 (GroupoidsOver.slice U), inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance⟩

end AlgebraicGeometry.AlgebraicStack
