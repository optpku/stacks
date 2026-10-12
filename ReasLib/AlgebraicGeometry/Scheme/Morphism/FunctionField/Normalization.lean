/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FunctionField.Normalization
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FunctionField

/-!
# Function-field comparison for normalization

This module records the factorization of the function-field extension map through an integral
scheme preserving the relevant generic points.
-/

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The function-field extension map induced by a generic-point-preserving morphism factors
through the source scheme. -/
theorem functionFieldExtensionMap_eq
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsIntegral X] [IsIntegral Y]
    (h_generic : f (genericPoint Y) = genericPoint X) :
    @Scheme.FunctionFieldExtension.map X _ Y.functionField _
        (f.functionFieldAlgebra h_generic) =
      Y.fromSpecStalk (genericPoint Y) ≫ f := sorry

end AlgebraicGeometry.Scheme.Hom

end
