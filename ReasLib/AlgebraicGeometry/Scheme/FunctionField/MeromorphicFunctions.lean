/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.MeromorphicFunction
public import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Rational functions as global meromorphic functions

On an integral scheme, rational functions determine global meromorphic sections through
comparison with the meromorphic stalk at the generic point.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsIntegral X]

/-- The canonical stalk map `K(X) ⟶ 𝒦_{X, η}` induced by `𝒪_X ⟶ 𝒦_X` at the generic
point. -/
def functionFieldToMeromorphicStalk :
    X.functionField ⟶
      X.toLocallyRingedSpace.meromorphicFunctionSheaf.presheaf.stalk (genericPoint X) :=
  (TopCat.Presheaf.stalkFunctor CommRingCat (genericPoint X)).map
    X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom.hom

/-- The germ map `Γ(X, 𝒦_X) ⟶ 𝒦_{X, η}` on global meromorphic functions. -/
def meromorphicGermGenericPoint :
    X.toLocallyRingedSpace.meromorphicFunctions ⟶
      X.toLocallyRingedSpace.meromorphicFunctionSheaf.presheaf.stalk (genericPoint X) :=
  X.toLocallyRingedSpace.meromorphicFunctionSheaf.presheaf.germ ⊤ (genericPoint X) trivial

/-- The canonical comparison `K(X) ⟶ Γ(X, 𝒦_X)`, sending a rational function to the unique
global meromorphic section whose germ at the generic point is its image in `𝒦_{X, η}`. -/
def functionFieldToMeromorphicFunctions :
    X.functionField ⟶ X.toLocallyRingedSpace.meromorphicFunctions :=
  functionFieldToMeromorphicStalk X ≫
    CommRingCat.ofHom
      { toFun := Function.invFun (meromorphicGermGenericPoint X).hom
        map_one' := sorry
        map_mul' := sorry
        map_zero' := sorry
        map_add' := sorry }

/-- The germ at the generic point of the meromorphic image of a rational function is the
canonical stalk map. -/
theorem functionFieldToMeromorphicFunctions_germ (f : X.functionField) :
    meromorphicGermGenericPoint X (functionFieldToMeromorphicFunctions X f) =
      functionFieldToMeromorphicStalk X f :=
  sorry

/-- The global meromorphic unit associated to a rational function. -/
def meromorphicUnitOfFunctionField (f : X.functionFieldˣ) :
    (X.toLocallyRingedSpace.meromorphicFunctions)ˣ :=
  Units.map (functionFieldToMeromorphicFunctions X).hom.toMonoidHom f

end AlgebraicGeometry.Scheme
