/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.K0.Module
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.K0'.Action

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

/-- The canonical derived tensor of a perfect complex with a coherent module in degree zero. -/
noncomputable def tensorObject
    (K : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace))
    (F : (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf).FullSubcategory) :
    RingedSpace.ModuleDerived X.toRingedSpace :=
  (@DerivedCategory.DerivedTensor.Right.functor
    (RingedSpace.Modules X.toRingedSpace) _ _ _ _ _
    (SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor X.toRingedSpace.sheaf)
    ((DerivedCategory.singleFunctor (RingedSpace.Modules X.toRingedSpace) (0 : ℤ)).obj F.obj)
    (SheafOfModules.RingedSite.moduleCategoryHasDerivedTensor
      X.toRingedSpace.sheaf).right).obj K.obj

/-- `tensorObject` is the canonical derived tensor product. -/
theorem tensorObject_def
    (K : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace))
    (F : (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf).FullSubcategory) :
    tensorObject X K F =
      (@DerivedCategory.DerivedTensor.Right.functor
        (RingedSpace.Modules X.toRingedSpace) _ _ _ _ _
        (SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor X.toRingedSpace.sheaf)
        ((DerivedCategory.singleFunctor (RingedSpace.Modules X.toRingedSpace) (0 : ℤ)).obj F.obj)
        (SheafOfModules.RingedSite.moduleCategoryHasDerivedTensor
          X.toRingedSpace.sheaf).right).obj K.obj := sorry

/-- The direct sum of the even cohomology sheaves of the derived tensor of a perfect complex
with a coherent module is coherent. -/
theorem evenTensorCohomology_isCoherent
    (K : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace))
    (F : (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf).FullSubcategory) :
    (∐ fun i : ℤ ↦ RingedSpace.ModuleDerived.cohomologySheaf
      (tensorObject X K F) (2 * i)).IsCoherent := sorry

/-- The direct sum of the odd cohomology sheaves of the derived tensor of a perfect complex
with a coherent module is coherent. -/
theorem oddTensorCohomology_isCoherent
    (K : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace))
    (F : (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf).FullSubcategory) :
    (∐ fun i : ℤ ↦ RingedSpace.ModuleDerived.cohomologySheaf
      (tensorObject X K F) (2 * i + 1)).IsCoherent := sorry

/-- The coherent direct sum of the even tensor-cohomology sheaves. -/
noncomputable def evenTensorCohomology
    (K : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace))
    (F : (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf).FullSubcategory) :
    (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf).FullSubcategory :=
  ⟨∐ fun i : ℤ ↦ RingedSpace.ModuleDerived.cohomologySheaf
      (tensorObject X K F) (2 * i),
    evenTensorCohomology_isCoherent X K F⟩

/-- The underlying module of `evenTensorCohomology` is the even tensor-cohomology sum. -/
theorem evenTensorCohomology_obj
    (K : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace))
    (F : (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf).FullSubcategory) :
    (evenTensorCohomology X K F).obj =
      ∐ fun i : ℤ ↦ RingedSpace.ModuleDerived.cohomologySheaf
        (tensorObject X K F) (2 * i) := sorry

/-- The coherent direct sum of the odd tensor-cohomology sheaves. -/
noncomputable def oddTensorCohomology
    (K : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace))
    (F : (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf).FullSubcategory) :
    (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf).FullSubcategory :=
  ⟨∐ fun i : ℤ ↦ RingedSpace.ModuleDerived.cohomologySheaf
      (tensorObject X K F) (2 * i + 1),
    oddTensorCohomology_isCoherent X K F⟩

/-- The underlying module of `oddTensorCohomology` is the odd tensor-cohomology sum. -/
theorem oddTensorCohomology_obj
    (K : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace))
    (F : (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf).FullSubcategory) :
    (oddTensorCohomology X K F).obj =
      ∐ fun i : ℤ ↦ RingedSpace.ModuleDerived.cohomologySheaf
        (tensorObject X K F) (2 * i + 1) := sorry

/-- The Euler class of the derived tensor of a perfect complex with a coherent module. -/
noncomputable def value
    (K : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace))
    (F : (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf).FullSubcategory) : K0' X :=
  ObjectProperty.GrothendieckGroup.of
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf)
      (evenTensorCohomology X K F) -
    ObjectProperty.GrothendieckGroup.of
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf)
      (oddTensorCohomology X K F)

/-- `value` is the even tensor-cohomology class minus the odd tensor-cohomology class. -/
theorem value_def
    (K : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace))
    (F : (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf).FullSubcategory) :
    value X K F =
      ObjectProperty.GrothendieckGroup.of
          (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf)
          (evenTensorCohomology X K F) -
        ObjectProperty.GrothendieckGroup.of
          (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf)
          (oddTensorCohomology X K F) := sorry

/-- For a fixed perfect complex, tensor Euler classes kill coherent Grothendieck relations. -/
theorem relations_le_ker_actOf
    (K : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace)) :
    ObjectProperty.GrothendieckGroup.relations
        (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) ≤
      (FreeAbelianGroup.lift (value X K)).ker := sorry

/-- The additive action of a fixed perfect complex on coherent `K₀'`. -/
noncomputable def actOf
    (K : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace)) : K0' X →+ K0' X :=
  ObjectProperty.GrothendieckGroup.lift (value X K) (relations_le_ker_actOf X K)

/-- `actOf` sends a coherent generator to its tensor Euler class. -/
theorem actOf_of
    (K : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace))
    (F : (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf).FullSubcategory) :
    actOf X K (ObjectProperty.GrothendieckGroup.of
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) F) = value X K F := sorry

/-- Perfect-complex classes defining `actOf` kill the triangulated Grothendieck relations. -/
theorem relations_le_ker_act :
    TriangulatedK0.relations
        (RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace)) ≤
      (FreeAbelianGroup.lift fun K :
        RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace) ↦ actOf X K).ker := sorry

/-- The explicit biadditive action of perfect `K₀` on coherent `K₀'` for a locally
Noetherian scheme. -/
noncomputable def act : K0 X →+ K0' X →+ K0' X :=
  TriangulatedK0.lift (actOf X) (relations_le_ker_act X)

/-- The explicit action computes by tensor Euler classes on perfect and coherent generators. -/
theorem act_of
    (K : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace))
    (F : (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf).FullSubcategory) :
    act X (TriangulatedK0.of K)
        (ObjectProperty.GrothendieckGroup.of
          (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) F) = value X K F := sorry

/-- On a Noetherian scheme, the explicit locally Noetherian action agrees with the existing
scalar action. -/
theorem act_eq_smul (X : Scheme.{u}) [IsNoetherian X] (a : K0 X) (m : K0' X) :
    act X a m = a • m := sorry

end AlgebraicGeometry.Scheme.K0'.Action
