/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback

/-!
# Relative ampleness near a proper fiber

An invertible module that is ample on one fiber of a proper morphism is relatively ample
over a neighborhood of that fiber.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.RelativelyAmple

/-- For a proper morphism, an invertible module that is ample on the fiber over a point is
relatively ample over an open neighborhood of that point. -/
@[stacks 0D2S]
theorem exists_morphismRestrict_of_isAmple_fiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (L : X.Modules) [L.Invertible] (y : Y)
    [Scheme.Modules.IsAmple ((Scheme.Modules.pullback (f.fiberι y)).obj L)] :
    ∃ V : Y.Opens, y ∈ V ∧ RelativelyAmple (f ∣_ V) (restrictToBasePreimage f L V) := sorry

end AlgebraicGeometry.RelativelyAmple
