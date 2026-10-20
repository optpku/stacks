/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Single
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.StructureSheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.Sections

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Modules
open DerivedCategory.TStructure Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/-- The reverse comparison `Lf^* 𝒪_X[0] ⟶ 𝒪_Y[0]` of derived pullback of the structure sheaf. -/
def structureSheafDerivedPullbackCounit {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    (pullback f).obj (structureSheafDerived X) ⟶ structureSheafDerived Y :=
  singlePullbackComparison f (SheafOfModules.unit (structureSheaf X)) 0 ≫
    (DerivedCategory.singleFunctor (Modules Y) 0).map (IdealSubobject.pullbackUnit f)

/-- Derived pullback of the structure sheaf in degree zero is bounded below by zero. -/
instance instIsGE_pullback_structureSheafDerived {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    ((pullback f).obj (structureSheafDerived X)).IsGE 0 := sorry

/-- The canonical unit `𝒪_Y[0] ⟶ Lf^* 𝒪_X[0]`, from the underived structure-sheaf unit,
the existing single-sheaf homology comparison, and `lowerCohomologyInclusion`. -/
def structureSheafDerivedPullbackUnit {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    structureSheafDerived Y ⟶ (pullback f).obj (structureSheafDerived X) :=
  (DerivedCategory.singleFunctor (Modules Y) 0).map
      (structureModulePullbackInv f ≫
        inv (singlePullbackHomologyComparison f
          (SheafOfModules.unit (structureSheaf X)) 0)) ≫
    lowerCohomologyInclusion ((pullback f).obj (structureSheafDerived X)) 0 inferInstance

/-- `structureSheafDerivedPullbackUnit` is `singleFunctor` of `structureModulePullbackInv`
followed by the inverse single-sheaf homology comparison and
`lowerCohomologyInclusion`. -/
theorem structureSheafDerivedPullbackUnit_eq {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    structureSheafDerivedPullbackUnit f =
      (DerivedCategory.singleFunctor (Modules Y) 0).map
          (structureModulePullbackInv f ≫
            inv (singlePullbackHomologyComparison f
              (SheafOfModules.unit (structureSheaf X)) 0)) ≫
        lowerCohomologyInclusion ((pullback f).obj (structureSheafDerived X)) 0
          inferInstance :=
  rfl

/-- The structure-sheaf derived pullback unit followed by its counit is the identity. -/
theorem structureSheafDerivedPullbackUnit_hom_inv_id {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    structureSheafDerivedPullbackUnit f ≫ structureSheafDerivedPullbackCounit f =
      𝟙 (structureSheafDerived Y) := sorry

/-- The structure-sheaf derived pullback counit followed by its unit is the identity. -/
theorem structureSheafDerivedPullbackUnit_inv_hom_id {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    structureSheafDerivedPullbackCounit f ≫ structureSheafDerivedPullbackUnit f =
      𝟙 ((pullback f).obj (structureSheafDerived X)) := sorry

/-- The unit `𝒪_Y[0] ⟶ Lf^* 𝒪_X[0]` is inverse to `structureSheafDerivedPullbackCounit`. -/
def structureSheafDerivedPullbackUnitIso {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    structureSheafDerived Y ≅ (pullback f).obj (structureSheafDerived X) where
  hom := structureSheafDerivedPullbackUnit f
  inv := structureSheafDerivedPullbackCounit f
  hom_inv_id := structureSheafDerivedPullbackUnit_hom_inv_id f
  inv_hom_id := structureSheafDerivedPullbackUnit_inv_hom_id f

/-- The hom of `structureSheafDerivedPullbackUnitIso` is `structureSheafDerivedPullbackUnit`. -/
theorem structureSheafDerivedPullbackUnitIso_hom {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    (structureSheafDerivedPullbackUnitIso f).hom =
      structureSheafDerivedPullbackUnit f :=
  rfl

/-- The inv of `structureSheafDerivedPullbackUnitIso` is `structureSheafDerivedPullbackCounit`. -/
theorem structureSheafDerivedPullbackUnitIso_inv {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    (structureSheafDerivedPullbackUnitIso f).inv =
      structureSheafDerivedPullbackCounit f :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
