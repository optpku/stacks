/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.QuasiCompact

/-! # Failure of quasi-coherent cohomology preservation by derived direct image -/

@[expose] public section

open AlgebraicGeometry CategoryTheory GroupoidsOver
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A quasi-compact quasi-separated morphism of algebraic stacks need not have
unbounded fppf derived direct image preserving locally quasi-coherent cohomology
with flat base change. -/
theorem not_forall_mapsDerivedLQCohFbc :
    ¬ ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
        [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
        [QuasiCompact f] [QuasiSeparated f], mapsDerivedLQCohFbc f := sorry

end AlgebraicGeometry.AlgebraicStack
