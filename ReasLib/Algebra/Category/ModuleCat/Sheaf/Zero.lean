/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Zero objects for sheaves of modules

The zero module sheaf is intrinsic to the category of modules over any sheaf of rings.  In
particular, its existence does not depend on a choice of sheafification, a presentation, or a
free-module construction.
-/

@[expose] public section

open CategoryTheory Limits

universe u v w t

namespace SheafOfModules

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- The category of sheaves of `R`-modules has a canonical zero object. -/
@[stacks 03DB "zero object", instance]
noncomputable instance instHasZeroObject :
    HasZeroObject (SheafOfModules.{t} R) :=
  hasZeroObject_of_hasTerminal_object

end SheafOfModules
