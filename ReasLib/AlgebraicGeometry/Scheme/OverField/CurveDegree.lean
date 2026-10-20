module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import ReasLib.AlgebraicGeometry.Scheme.OverField.FunctionField
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

@[expose] public section

open AlgebraicGeometry CategoryTheory Topology

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]
variable {X Y : SchemeOverField k} [Curve X] [Curve Y]

/-- The induced map of function fields along a dominant morphism of curves over `k`. -/
noncomputable def curveHomFunctionFieldMap (π : X ⟶ Y) [IsDominant π.left] :
    Y.left.functionField →+* X.left.functionField where
  toFun y :=
    (π.left.stalkMap (genericPoint X.left)).hom
      (Function.invFun
        (Y.left.presheaf.stalkSpecializes
          (genericPoint_specializes (π.left (genericPoint X.left)))).hom y)
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- The function-field algebra structure along a dominant morphism of curves over `k`. -/
@[reducible]
noncomputable def curveHomFunctionFieldAlgebra (π : X ⟶ Y) [IsDominant π.left] :
    Algebra Y.left.functionField X.left.functionField :=
  (curveHomFunctionFieldMap π).toAlgebra

/-- The degree of a dominant morphism of curves, as the function-field extension degree. -/
noncomputable def curveHomDegree (π : X ⟶ Y) [IsDominant π.left] : ℕ :=
  @Module.finrank Y.left.functionField X.left.functionField _ _
    (RingHom.toModule (curveHomFunctionFieldMap π))

/-- Unfold `curveHomDegree` as a function-field `Module.finrank`. -/
theorem curveHomDegree_def (π : X ⟶ Y) [IsDominant π.left] :
    curveHomDegree π =
      @Module.finrank Y.left.functionField X.left.functionField _ _
        (RingHom.toModule (curveHomFunctionFieldMap π)) := sorry

/-- A dominant morphism of curves has positive degree. -/
theorem curveHomDegree_pos (π : X ⟶ Y) [IsDominant π.left] :
    0 < curveHomDegree π := sorry

/-- For a dominant morphism `π`, the function-field map is the stalk map after inverting specialization. -/
theorem curveHomFunctionFieldMap_apply (π : X ⟶ Y) [IsDominant π.left]
    (y : Y.left.functionField) :
    curveHomFunctionFieldMap π y =
      (π.left.stalkMap (genericPoint X.left)).hom
        (Function.invFun
          (Y.left.presheaf.stalkSpecializes
            (genericPoint_specializes (π.left (genericPoint X.left)))).hom y) := sorry

end AlgebraicGeometry.SchemeOverField
