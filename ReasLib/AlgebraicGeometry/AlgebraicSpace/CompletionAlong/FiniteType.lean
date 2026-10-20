module

public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.FiniteType

/-!
# Locally of finite type morphisms of completions

A locally finite type morphism of algebraic spaces induces a locally finite type
morphism of formal completions along a closed subset.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A locally finite type morphism of algebraic spaces induces a locally finite
type morphism from the completion along the inverse image of a closed subset to
the completion along that subset. -/
instance locallyOfFiniteType_completionAlongMap {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} (f : X' ⟶ X) [AlgebraicSpace.LocallyOfFiniteType f]
    (T : Closeds (Points X)) :
    FormalAlgebraicSpace.LocallyOfFiniteType (completionAlong.map f T) :=
  sorry

/-- The relative diagonal of `completionAlong.map f T` is locally of finite type
when `f` is locally of finite type. -/
instance instLocallyOfFiniteType_diagonal_completionAlongMap
    {S : Scheme.{u}} {X X' : AlgebraicSpace S} (f : X' ⟶ X)
    [AlgebraicSpace.LocallyOfFiniteType f] (T : Closeds (Points X)) :
    FormalAlgebraicSpace.LocallyOfFiniteType
      (pullback.diagonal (completionAlong.map f T)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
