module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InternalHom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.StructureModule
public import Mathlib.LinearAlgebra.Span.Basic

/-! # Scalar multiplication of local module morphisms -/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.InternalHom

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {F G : Modules X}

/-- Scalar multiplication of a module morphism defines a morphism from the tensor unit
to the sheaf of local module morphisms. -/
def scalarMap (g : F ⟶ G) : 𝟙_ (Modules X) ⟶ obj F G :=
  (structureModuleIsoTensorUnit X).inv ≫
    (structureModuleIsoRestrictCommUnit X).hom ≫
    (ofCommModules X).map
      { val :=
          { app := fun U => ModuleCat.ofHom (R := (commStructureSheaf X).obj.obj U)
              (X := (SheafOfModules.RingedSite.unitModule
                (smallEtaleTopology X) (commStructureSheaf X)).val.obj U)
              (Y := sectionModule F G U.unop)
              (LinearMap.toSpanSingleton
                ((commStructureSheaf X).obj.obj U) (sectionModule F G U.unop)
                ((sectionEquiv F G U.unop).symm (g.over U.unop)))
            naturality := sorry } }

/-- On an étale chart, the scalar map sends a scalar to its multiple of the small code
of the restricted module morphism, after the canonical tensor-unit comparisons. -/
theorem scalarMap_apply (g : F ⟶ G) (U : smallEtaleSite X)
    (r : (𝟙_ (Modules X)).val.obj (op U)) :
    (scalarMap g).val.app (op U) r =
      (LinearMap.toSpanSingleton
        ((commStructureSheaf X).obj.obj (op U)) (sectionModule F G U)
        ((sectionEquiv F G U).symm (g.over U)))
        ((structureModuleIsoRestrictCommUnit X).hom.val.app (op U)
          ((structureModuleIsoTensorUnit X).inv.val.app (op U) r)) := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.InternalHom
