/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Single
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.StructureSheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.StructureModule
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSubobject.Pullback

/-! # Derived pullback of the structure sheaf -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}}

/-- The canonical comparison from derived pullback of the structure sheaf to the
structure sheaf on the source. -/
def pullbackStructureSheafMap {X Y : AlgebraicSpace S} (h : X ⟶ Y) :
    (pullback h).obj (structureSheaf Y) ⟶ structureSheaf X :=
  ObjectProperty.homMk <|
    (pullback.cellModelInclusionIso h).hom.app (structureSheaf Y) ≫
      (ModuleDerived.pullback h).map (structureSheafUnitIso Y).hom ≫
        ModuleDerived.singlePullbackComparison h (tensorUnit (Modules Y)) 0 ≫
          (DerivedCategory.singleFunctor (Modules X) 0).map
            ((Modules.pullback h).map (Modules.structureModuleIsoTensorUnit Y).inv ≫
              IdealSubobject.pullbackUnit h ≫
                (Modules.structureModuleIsoTensorUnit X).hom) ≫
            (structureSheafUnitIso X).inv

/-- The structure-sheaf pullback comparison is the single-sheaf comparison followed by
the degree-zero image of the ordinary structure-module pullback map. -/
theorem pullbackStructureSheafMap_spec {X Y : AlgebraicSpace S} (h : X ⟶ Y) :
    (pullbackStructureSheafMap h).hom =
      (pullback.cellModelInclusionIso h).hom.app (structureSheaf Y) ≫
        (ModuleDerived.pullback h).map (structureSheafUnitIso Y).hom ≫
          ModuleDerived.singlePullbackComparison h (tensorUnit (Modules Y)) 0 ≫
            (DerivedCategory.singleFunctor (Modules X) 0).map
              ((Modules.pullback h).map (Modules.structureModuleIsoTensorUnit Y).inv ≫
                IdealSubobject.pullbackUnit h ≫
                  (Modules.structureModuleIsoTensorUnit X).hom) ≫
              (structureSheafUnitIso X).inv :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
