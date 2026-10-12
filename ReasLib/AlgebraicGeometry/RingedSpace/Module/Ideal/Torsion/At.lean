/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.FiniteFree
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Ideal.Torsion
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pointwise ideal-torsion freeness

This file records the pointwise form of torsion freeness needed by local calculations.  It avoids
choosing a generator of a locally principal ideal and is weaker than requiring the entire torsion
sheaf to vanish.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.IdealSheaf

variable {X : RingedSpace.{u}}

/-- The stalk at `x` of the `I`-torsion subsheaf of `M` vanishes. -/
@[stacks 0GTA "pointwise ideal-torsion freeness"]
def IsTorsionFreeAt
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (M : X.Modules) (x : X) : Prop :=
  IsZero (stalkModuleCat
    (SheafOfModules.RingedSite.IdealSheaf.torsion (O := X.sheaf) I M) x)

/-- Pointwise torsion freeness is equivalent to vanishing of the usual submodule annihilated by
the stalk ideal. -/
@[stacks 0GTA "pointwise torsion-freeness criterion"]
theorem isTorsionFreeAt_iff_stalkSubmodule_eq_bot
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (M : X.Modules) (x : X)
    [(SheafOfModules.RingedSite.TensorPower.sheaf
      X.sheaf (I : X.Modules) 1).IsFinitePresentation] :
    IsTorsionFreeAt I M x ↔ PowerTorsion.stalkSubmodule I M 1 x = ⊥ := sorry

namespace IsRegularPrincipal

/-- A free stalk has no torsion for a locally principal regular ideal. -/
theorem isTorsionFreeAt_of_free
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [IsRegularPrincipal I] (M : X.Modules) (x : X)
    [Module.Free (X.presheaf.stalk x) (stalkModuleCat M x)] :
    IsTorsionFreeAt I M x := sorry

/-- A finite-free stalk has no torsion for a locally principal regular ideal.  This source-facing
bridge accepts the object-property formulation used by cohomology-stalk APIs. -/
@[stacks 0GTA "finite-free stalk is ideal-torsion-free"]
theorem isTorsionFreeAt_of_finiteFree
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [IsRegularPrincipal I] (M : X.Modules) (x : X)
    (hM : ModuleCat.finiteFree (X.presheaf.stalk x) (stalkModuleCat M x)) :
    IsTorsionFreeAt I M x := sorry

end IsRegularPrincipal

end AlgebraicGeometry.RingedSpace.IdealSheaf
