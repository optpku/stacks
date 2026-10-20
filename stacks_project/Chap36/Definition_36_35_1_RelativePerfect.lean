module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Relative

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

#check
  (@AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfectOver :
    ∀ {X S : RingedSpace.{u}} (f : X ⟶ S)
      [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase f).carrier,
        DerivedCategory.DerivedTensor.Right.Has
          (C := RingedSpace.Modules
            ((RingedSpace.Hom.inverseImageBase f).restrict U.isOpenEmbedding))],
      RingedSpace.ModuleDerived X → Prop)
