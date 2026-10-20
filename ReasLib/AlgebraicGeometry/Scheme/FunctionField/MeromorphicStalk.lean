module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.MeromorphicFunction
public import Mathlib.AlgebraicGeometry.FunctionField

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsIntegral X]

/-- The inverse function of the canonical map to the generic meromorphic stalk is a left
inverse on the function field. -/
theorem functionFieldMeromorphicStalk_left_inv :
    Function.LeftInverse
      (Function.invFun (algebraMap X.functionField
        (X.toLocallyRingedSpace.meromorphicFunctionSheaf.presheaf.stalk (genericPoint X))))
      (algebraMap X.functionField
        (X.toLocallyRingedSpace.meromorphicFunctionSheaf.presheaf.stalk (genericPoint X))) := sorry

/-- The inverse function of the canonical map to the generic meromorphic stalk is a right
inverse on that stalk. -/
theorem functionFieldMeromorphicStalk_right_inv :
    Function.RightInverse
      (Function.invFun (algebraMap X.functionField
        (X.toLocallyRingedSpace.meromorphicFunctionSheaf.presheaf.stalk (genericPoint X))))
      (algebraMap X.functionField
        (X.toLocallyRingedSpace.meromorphicFunctionSheaf.presheaf.stalk (genericPoint X))) := sorry

/-- The canonical ring equivalence from the function field to the generic meromorphic stalk
has the structure-sheaf algebra map as its forward map. -/
def functionFieldMeromorphicStalkEquiv :
    X.functionField ≃+*
      X.toLocallyRingedSpace.meromorphicFunctionSheaf.presheaf.stalk (genericPoint X) where
  toFun := algebraMap X.functionField
    (X.toLocallyRingedSpace.meromorphicFunctionSheaf.presheaf.stalk (genericPoint X))
  invFun := Function.invFun (algebraMap X.functionField
    (X.toLocallyRingedSpace.meromorphicFunctionSheaf.presheaf.stalk (genericPoint X)))
  left_inv := functionFieldMeromorphicStalk_left_inv X
  right_inv := functionFieldMeromorphicStalk_right_inv X
  map_mul' := (algebraMap X.functionField
    (X.toLocallyRingedSpace.meromorphicFunctionSheaf.presheaf.stalk (genericPoint X))).map_mul
  map_add' := (algebraMap X.functionField
    (X.toLocallyRingedSpace.meromorphicFunctionSheaf.presheaf.stalk (genericPoint X))).map_add

end AlgebraicGeometry.Scheme
