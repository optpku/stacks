/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Monoidal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSiteTensorUnit

/-! # The structure module and the tensor unit

The actual structure-sheaf ring comparison supplies both section maps of the
structure-module isomorphism. Its tensor-unit comparison uses the canonical
transported monoidal structure.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite

noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/-- The structure-module value of `X` at an étale object. -/
abbrev structureModuleSection (U : (smallEtaleSite X)ᵒᵖ) :=
  (SheafOfModules.unit (structureSheaf X)).val.obj U

/-- The restricted commutative structure-module value of `X` at an étale object. -/
abbrev restrictCommUnitSection (U : (smallEtaleSite X)ᵒᵖ) :=
  ((ofCommModules X).obj
      (unitModule (smallEtaleTopology X) (commStructureSheaf X))).val.obj U

/-- The component of the structure-module comparison at an étale object. -/
noncomputable def structureModuleIsoRestrictCommUnitApp (U : (smallEtaleSite X)ᵒᵖ) :
    structureModuleSection X U ⟶ restrictCommUnitSection X U :=
  ModuleCat.ofHom
    (X := structureModuleSection X U)
    (Y := restrictCommUnitSection X U)
    { toFun := ((commRingSheafIso X).inv.hom.app U).hom
      map_add' := sorry
      map_smul' := sorry }

/-- The inverse component of the structure-module comparison at an étale object. -/
noncomputable def structureModuleIsoRestrictCommUnitAppInv (U : (smallEtaleSite X)ᵒᵖ) :
    restrictCommUnitSection X U ⟶ structureModuleSection X U :=
  ModuleCat.ofHom
    (X := restrictCommUnitSection X U)
    (Y := structureModuleSection X U)
    { toFun := ((commRingSheafIso X).hom.hom.app U).hom
      map_add' := sorry
      map_smul' := sorry }

/-- The structure module of `X` as restriction of scalars of the commutative
structure module along `commRingSheafIso`. -/
noncomputable def structureModuleIsoRestrictCommUnit :
    SheafOfModules.unit (structureSheaf X) ≅
      (ofCommModules X).obj
        (unitModule (smallEtaleTopology X) (commStructureSheaf X)) where
  hom :=
    { val :=
        { app := fun U ↦ structureModuleIsoRestrictCommUnitApp X U
          naturality := sorry } }
  inv :=
    { val :=
        { app := fun U ↦ structureModuleIsoRestrictCommUnitAppInv X U
          naturality := sorry } }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The structure module of an algebraic space is canonically isomorphic to the
tensor unit of `X.Modules`. -/
noncomputable def structureModuleIsoTensorUnit :
    SheafOfModules.unit (structureSheaf X) ≅ 𝟙_ X.Modules :=
  structureModuleIsoRestrictCommUnit X ≪≫
    (ofCommModules X).mapIso unitIsoTensorUnit.{u + 1, u, u}

end AlgebraicGeometry.AlgebraicSpace.Modules
