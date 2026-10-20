/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.LocalSectionMul
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Local-section actions on module sheaves over ringed spaces

This file relates the generic presheaf-level section action to restriction and germ maps on the
opens site of a ringed space.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}} (M : X.Modules)

/-- On a slice object `W ⟶ U`, the local-section action is multiplication by the restriction of
the section from `U` to `W`. -/
@[stacks 03EM "restriction formula"]
theorem sectionAction_app
    (U W : Opens X) (i : W ⟶ U) (s : X.presheaf.obj (op U))
    (t : M.val.obj (op W)) :
    ((SheafOfModules.sectionAction X.sheaf M U s).val.app (op (Over.mk i))) t =
      X.presheaf.map i.op s • t := sorry

/-- Taking a germ intertwines the local-section action with scalar multiplication by the germ of
the acting section. -/
@[stacks 03EM "germ formula"]
theorem sectionAction_germ
    (U W : Opens X) (i : W ⟶ U) (y : X) (hy : y ∈ W)
    (s : X.presheaf.obj (op U)) (t : M.val.obj (op W)) :
    TopCat.Presheaf.germ M.val.presheaf W y hy
        (((SheafOfModules.sectionAction X.sheaf M U s).val.app (op (Over.mk i))) t) =
      X.presheaf.germ U y (i.le hy) s •
        TopCat.Presheaf.germ M.val.presheaf W y hy t := sorry

end AlgebraicGeometry.RingedSpace
