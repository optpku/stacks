/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FunctionField

/-!
# Maps on function-field units

This file provides the map on units induced by a morphism's map on function fields.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The map on function-field units induced by a generic-point-preserving morphism of integral
schemes. -/
noncomputable def functionFieldUnitsMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y]
    (h_generic : f (genericPoint X) = genericPoint Y) :
    Y.functionFieldˣ →* X.functionFieldˣ :=
  Units.map (f.functionFieldMap h_generic)

/-- The underlying value of the induced map on function-field units is obtained by applying
the function-field ring homomorphism. -/
theorem functionFieldUnitsMap_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y]
    (h_generic : f (genericPoint X) = genericPoint Y) (g : Y.functionFieldˣ) :
    (f.functionFieldUnitsMap h_generic g : X.functionField) =
      f.functionFieldMap h_generic (g : Y.functionField) := sorry

end AlgebraicGeometry.Scheme.Hom
