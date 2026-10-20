module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.WellNighAffine

/-!
# Well-nigh affine algebraic stacks

An algebraic stack is well-nigh affine when it admits a surjective, flat,
finite, and finitely presented atlas from an affine scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

#check (IsWellNighAffine : ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X], Prop)

#check (IsWellNighAffine.spec : ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsWellNighAffine X],
    ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
      IsAffine U.left ∧ AlgebraicStack.Surjective p ∧ AlgebraicStack.Flat p ∧
        AlgebraicStack.IsFinite p ∧ AlgebraicStack.FinitePresentation p)

#check (IsWellNighAffine.of : ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {U : Over S}
    [IsAffine U.left] (p : GroupoidsOver.slice U ⟶ X)
    [AlgebraicStack.Surjective p] [AlgebraicStack.Flat p]
    [AlgebraicStack.IsFinite p] [AlgebraicStack.FinitePresentation p],
    IsWellNighAffine X)

#check (instIsWellNighAffine_slice : ∀ {S : Scheme.{u}} (U : Over S)
    [IsAffine U.left], IsWellNighAffine (GroupoidsOver.slice U))

end AlgebraicGeometry.AlgebraicStack
