/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSiteTensorUnit
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Monoidal
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The tensor unit of module sheaves on a ringed space

This is the ringed-space specialization of the canonical ringed-site comparison.  It removes the
need for downstream files to carry a separate `UnitIsSheafifiedUnit` hypothesis.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The structure module of a ringed space is canonically isomorphic to the tensor unit. -/
@[stacks 03L6 "tensor unit on a ringed space"]
noncomputable abbrev unitIsoTensorUnit (X : RingedSpace.{u}) :
    (SheafOfModules.unit X.ringCatSheaf : X.Modules) ≅ 𝟙_ (X.Modules) :=
  SheafOfModules.RingedSite.unitIsoTensorUnit
    (J := Opens.grothendieckTopology X) (𝒪 := X.sheaf)

/-- The canonical morphism from the ambient tensor unit to the structure module of a ringed
space. -/
@[stacks 03L6 "tensor unit to the structure module of a ringed space"]
noncomputable abbrev tensorUnitToUnitModule (X : RingedSpace.{u}) :
    𝟙_ (X.Modules) ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
  SheafOfModules.RingedSite.tensorUnitToUnitModule
    (J := Opens.grothendieckTopology X) (𝒪 := X.sheaf)

/-- The canonical morphism from the structure module of a ringed space to the ambient tensor
unit. -/
@[stacks 03L6 "structure module to the tensor unit of a ringed space"]
noncomputable abbrev unitModuleToTensorUnit (X : RingedSpace.{u}) :
    (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ 𝟙_ (X.Modules) :=
  SheafOfModules.RingedSite.unitModuleToTensorUnit
    (J := Opens.grothendieckTopology X) (𝒪 := X.sheaf)

/-- The forward map of the ringed-space tensor-unit isomorphism is the named structure-module
comparison. -/
@[simp, stacks 03L6 "ringed-space tensor unit isomorphism forward map"]
theorem unitIsoTensorUnit_hom (X : RingedSpace.{u}) :
    (unitIsoTensorUnit X).hom = unitModuleToTensorUnit X := sorry

/-- The inverse map of the ringed-space tensor-unit isomorphism is the named tensor-unit
comparison. -/
@[simp, stacks 03L6 "ringed-space tensor unit isomorphism inverse map"]
theorem unitIsoTensorUnit_inv (X : RingedSpace.{u}) :
    (unitIsoTensorUnit X).inv = tensorUnitToUnitModule X := sorry

/-- The explicit ringed-space tensor-unit comparison is the inverse of the canonical unit
isomorphism. -/
@[simp, stacks 03L6 "ringed-space tensor unit inverse bridge"]
theorem tensorUnitToUnitModule_eq (X : RingedSpace.{u}) :
    tensorUnitToUnitModule X = (unitIsoTensorUnit X).inv := sorry

/-- The ringed-space tensor-unit comparison followed by its named inverse is the identity. -/
@[simp, stacks 03L6 "ringed-space tensor unit forward-inverse law"]
theorem tensorUnitToUnitModule_hom_inv_id (X : RingedSpace.{u}) :
    tensorUnitToUnitModule X ≫ unitModuleToTensorUnit X = 𝟙 _ := sorry

/-- The named inverse followed by the ringed-space tensor-unit comparison is the identity. -/
@[simp, stacks 03L6 "ringed-space tensor unit inverse-forward law"]
theorem tensorUnitToUnitModule_inv_hom_id (X : RingedSpace.{u}) :
    unitModuleToTensorUnit X ≫ tensorUnitToUnitModule X = 𝟙 _ := sorry

end AlgebraicGeometry.RingedSpace


