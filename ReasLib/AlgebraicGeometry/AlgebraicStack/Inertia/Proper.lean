module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation.Object
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.AbsoluteTransformations.Maps.Construction

/-!
# Proper inertia of separated algebraic stacks

Absolute or relative separation implies properness of the inertia morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids.Inertia (forget)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- If an algebraic stack is separated over `S`, then its inertia morphism is
proper as a morphism representable by algebraic spaces. -/
theorem forget_has_proper_of_isSeparatedOver {S : Scheme.{u}}
    {Y : GroupoidsOver S} [AlgebraicStack Y] [IsSeparatedOver Y] :
    Groupoids.Hom.has (@AlgebraicSpace.Proper S)
      (forget.{u + 1, u, u, u + 1} Y) :=
  sorry

/-- If an algebraic stack is separated, then its inertia morphism is proper as
a morphism representable by algebraic spaces. -/
theorem forget_has_proper_of_isSeparated {S : Scheme.{u}} {Y : GroupoidsOver S}
    [AlgebraicStack Y] [IsSeparated Y] :
    Groupoids.Hom.has (@AlgebraicSpace.Proper S)
      (forget.{u + 1, u, u, u + 1} Y) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
