module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FunctionField
public import Mathlib.FieldTheory.Separable

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A dominant morphism of integral schemes has a separable function-field extension when
the algebra structure induced by its map on function fields is separable. -/
def SeparableFunctionFieldExtension {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [IsDominant f] : Prop :=
  @Algebra.IsSeparable Y.functionField X.functionField inferInstance inferInstance
    (f.functionFieldAlgebra f.map_genericPoint_eq_of_isDominant)

end AlgebraicGeometry.Scheme.Hom
