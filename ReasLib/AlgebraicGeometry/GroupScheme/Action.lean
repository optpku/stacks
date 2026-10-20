/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import ReasLib.AlgebraicGeometry.GroupScheme

@[expose] public section

universe u

open CategoryTheory
open MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.GroupScheme

/-- The category of actions of a group scheme over a scheme, with equivariant morphisms. -/
abbrev Action {S : Scheme.{u}} (G : Grp (Over S)) : Type (u + 1) :=
  Mod (Over S) G.X

/-- The trivial action of a group scheme on the terminal scheme over its base. -/
def trivialAction {S : Scheme.{u}} (G : GroupScheme S) : Action G :=
  Mod.trivialAction G.toMon (𝟙_ (Over S))

/-- The underlying object of the trivial action is the terminal scheme over the base. -/
theorem trivialAction_X {S : Scheme.{u}} (G : GroupScheme S) :
    (trivialAction G).X = 𝟙_ (Over S) := rfl

end AlgebraicGeometry.GroupScheme
