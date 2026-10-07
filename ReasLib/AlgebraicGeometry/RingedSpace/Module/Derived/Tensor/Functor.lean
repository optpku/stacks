module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Tensor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Monoidal
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

/-- The canonical fixed-left derived tensor functor on derived module sheaves over a ringed
space. -/
noncomputable def derivedTensorLeft {X : RingedSpace.{u}} (E : ModuleDerived X) :
    ModuleDerived X ⥤ ModuleDerived X :=
  @DerivedCategory.DerivedTensor.Left.functor X.Modules _ _ _ _ _
    (fun K L ↦ SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor X.sheaf K L) E
    (SheafOfModules.RingedSite.moduleCategoryHasDerivedTensor X.sheaf).left

end AlgebraicGeometry.RingedSpace.ModuleDerived

end
