/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Ample.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Fiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Restrict

/-!
# Relative ampleness near a fibre of a proper algebraic space

An invertible module that is ample on a schematic fibre of a proper morphism
is relatively ample over an open neighbourhood of the corresponding base point.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- For a proper algebraic space over a Noetherian scheme, an invertible module
that is ample on a fibre represented by a scheme is relatively ample after
restriction to an open neighbourhood of the corresponding base point. -/
theorem RelativelyAmple.exists_morphismRestrict_of_isAmple_fiber
    {Y : Scheme.{u}} [IsNoetherian Y] {X : AlgebraicSpace Y}
    (f : X ⟶ ofOver (Over.mk (𝟙 Y))) [Proper f]
    (L : X.Modules) [isInvertibleObject L] (y : Y)
    {T : Over Y} (e : fiber f y ≅ ofOver T)
    [Scheme.Modules.IsAmple (moduleOnScheme f y e L)] :
    ∃ V : Y.Opens, y ∈ V ∧
      RelativelyAmple (morphismRestrict f V)
        (Modules.restrictToBasePreimage f L V) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
