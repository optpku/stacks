module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Gerbe
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 101.28.1 (1): a morphism `f : X ⟶ Y` of algebraic stacks makes
`X` a gerbe over `Y` when `f` is a gerbe morphism of stacks in groupoids over
`(Sch/S)_fppf`. -/
@[stacks 06QC] #check (AlgebraicGeometry.AlgebraicStack.Gerbe :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y], (X ⟶ Y) → Prop)

/- Definition 101.28.1 (2): an algebraic stack `X` is a gerbe if there exists a
morphism `X ⟶ A.toGroupoids` to an algebraic space which turns `X` into a
gerbe over that space. -/
@[stacks 06QC] #check (AlgebraicGeometry.AlgebraicStack.IsGerbe :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X], Prop)
