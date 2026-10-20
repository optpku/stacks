module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Gerbe
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack

/-!
# Gerbes of algebraic stacks

A morphism of algebraic stacks is a gerbe over its target when it is a gerbe
morphism of categories fibred in groupoids on the big fppf site. An algebraic
stack is a gerbe when it is a gerbe over some algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

#check (AlgebraicGeometry.AlgebraicStack.Gerbe :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y], (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.AlgebraicStack.IsGerbe :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X], Prop)
