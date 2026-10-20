module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.VersalRing.Realization

/-! # Complete local realizations of versal rings -/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing
open FiberedCategoryOver.Groupoids
open GroupoidsOver
open AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

#check (AlgebraicGeometry.AlgebraicStack.RealizesVersalRing :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (A : CompleteLocalSAlgebra S) (x : CompleteLocalObject X),
    Prop)

#check (AlgebraicGeometry.AlgebraicStack.RealizesVersalRing.iff :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (A : CompleteLocalSAlgebra S) (x : CompleteLocalObject X),
    RealizesVersalRing x0 A x ↔
      x.base = A ∧ StageOneCompatible x0 (FormalObject.restriction x) ∧
        GroupoidsOver.FormalObject.IsVersal (FormalObject.restriction x))

#check (AlgebraicGeometry.AlgebraicStack.RealizesVersalRing.toIsVersalRing :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    [AlgebraicStack X]
    (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (A : CompleteLocalSAlgebra S)
    [Fact (∃ x : CompleteLocalObject X, RealizesVersalRing x0 A x)],
    IsVersalRing x0 A)

