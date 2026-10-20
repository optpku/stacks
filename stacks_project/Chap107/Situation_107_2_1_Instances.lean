module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Base
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Base

/-!
# Identity fibration of a scheme as an algebraic stack

The universe-resized identity fibration on `Over S` is an algebraic stack, so
the canonical structure morphism of an algebraic stack over `S` may carry
morphism properties such as locally of finite type.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicStack

#check (AlgebraicGeometry.AlgebraicStack.base : ∀ (S : Scheme.{u}),
  AlgebraicStack (FiberedCategoryOver.Groupoids.base.{u + 1, u, u + 1} (Over S)))

end AlgebraicGeometry.AlgebraicStack
