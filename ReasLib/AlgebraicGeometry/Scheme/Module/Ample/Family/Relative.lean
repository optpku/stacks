/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Family
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative

/-!
# Ample families from relatively ample modules

This file relates ample families on a target scheme to relative ampleness of
modules on the source scheme.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme.Modules.AmpleFamily

/-- An ample family on the target of a scheme morphism and a relatively ample module on its
source yield an ample family on the source. -/
theorem exists_of_relativelyAmple {X Y : Scheme.{u}} {ι : Type v}
    (f : X ⟶ Y) (M : ι → Y.Modules) (hM : AmpleFamily M)
    (hL : ∃ L : X.Modules, RelativelyAmple f L) :
    ∃ (κ : Type (max u v)) (N : κ → X.Modules), AmpleFamily N := sorry

end AlgebraicGeometry.Scheme.Modules.AmpleFamily
