module

public import Mathlib.RingTheory.Norm.Defs
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.FunctionFieldDegree

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The norm on function-field units induced by a dominant morphism of integral schemes. -/
noncomputable def inducedFunctionFieldNorm {X Y : Scheme.{u}} (p : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [IsDominant p] : X.functionFieldˣ →* Y.functionFieldˣ :=
  -- Local instance justification (instance diamond): the algebra structure is determined by `p`, and distinct dominant morphisms can induce competing structures.
  letI : Algebra Y.functionField X.functionField :=
    p.functionFieldAlgebra p.map_genericPoint_eq_of_isDominant
  Units.map (Algebra.norm Y.functionField)

/-- The underlying value of the induced norm on units is the algebra norm. -/
theorem inducedFunctionFieldNorm_apply {X Y : Scheme.{u}} (p : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [IsDominant p] (f : X.functionFieldˣ) :
    -- Local instance justification (instance diamond): the algebra structure is determined by `p`, and distinct dominant morphisms can induce competing structures.
    letI : Algebra Y.functionField X.functionField :=
      p.functionFieldAlgebra p.map_genericPoint_eq_of_isDominant
    (p.inducedFunctionFieldNorm f : Y.functionField) =
      Algebra.norm Y.functionField (f : X.functionField) := sorry

end AlgebraicGeometry.Scheme.Hom
