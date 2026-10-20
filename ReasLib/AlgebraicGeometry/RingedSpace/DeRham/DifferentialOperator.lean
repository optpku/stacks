/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DeRham.DifferentialOperator
public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham
import Mathlib.Tactic.CrossRefAttribute

/-!
# Differential-operator order of ringed-space de Rham differentials

This file specializes the reusable ringed-site order bound to relative de Rham complexes of
morphisms of ringed spaces.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.DeRham

variable {X S : RingedSpace.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat]

/-- Lemma 17.30.5 (0G3Z): every relative de Rham differential of a morphism of ringed spaces is
a differential operator of order at most one. -/
@[stacks 0G3Z]
theorem d_isOrderOne (f : X ⟶ S) (p : ℕ) :
    IsDifferentialOperatorOfOrder (J := Opens.grothendieckTopology X)
      (structureMap f) (d f p) 1 := sorry

end AlgebraicGeometry.RingedSpace.DeRham
