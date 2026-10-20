/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.FinitePresentation
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Presentation
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Point.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finitely presented modules on a ringed point

The equivalence between modules over `R` and module sheaves on `RingedPoint.of R` preserves and
reflects finite presentation.  This is the point-level owner used by associated-sheaf
constructions.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedPoint.Module

variable (R : Type u) [CommRing R]

/-- A module is finitely presented exactly when its corresponding sheaf on the ringed point is
finitely presented. -/
@[stacks 01BR "finite presentation on a ringed point"]
theorem sheaf_isFinitePresentation_iff (M : ModuleCat.{u} R) :
    (sheaf R M).IsFinitePresentation ↔ Module.FinitePresentation R M := sorry

/-- A finitely presented module gives a finitely presented module sheaf on the ringed point. -/
@[stacks 01BR "finitely presented point module sheaf"]
instance sheaf_isFinitePresentation (M : ModuleCat.{u} R)
    [Module.FinitePresentation R M] :
    (sheaf R M).IsFinitePresentation := sorry

end AlgebraicGeometry.RingedPoint.Module
