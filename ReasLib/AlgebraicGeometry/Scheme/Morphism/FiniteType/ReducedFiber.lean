/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Properties
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
import Mathlib.Tactic.CrossRefAttribute

/-!
# Reduced fibers of finite-type morphisms

This file relates nonreducedness of the generic fiber to nonreducedness of fibers over an open
subset of an irreducible target.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom.FiniteType

/-- If the generic fiber of a finite-type morphism to an irreducible scheme is nonreduced, then
all fibers over some nonempty open subset are nonreduced. -/
@[stacks 0575]
theorem exists_open_not_isReduced_fiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) [FiniteType f] [IrreducibleSpace Y]
    (hη : ¬ IsReduced (f.fiber (genericPoint Y))) :
    ∃ V : Y.Opens, Nonempty V ∧ ∀ y : Y, y ∈ V → ¬ IsReduced (f.fiber y) := sorry

end AlgebraicGeometry.Scheme.Hom.FiniteType
