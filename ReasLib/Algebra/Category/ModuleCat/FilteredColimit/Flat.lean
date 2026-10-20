/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.FilteredColimit.Mono
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat modules and filtered colimits

Filtered colimits of flat modules are flat.  The cocone theorem is the reusable core statement;
the named instance specializes it to the canonical colimit chosen by the category-theory API.

@stack 05UT
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace ModuleCat.FilteredColimits

variable {R : Type u} [CommRing R]
variable {J : Type v} [SmallCategory J]
variable (F : J ⥤ ModuleCat.{max v u, u} R)

/-- Lemma 10.39.3 (05UT): the point of a filtered colimit cocone of flat modules is flat. -/
@[stacks 05UT "colimit cocone"]
theorem flat_of_isColimit [IsFiltered J] (c : Cocone F) (hc : IsColimit c)
    [∀ j, Module.Flat R (F.obj j)] :
    Module.Flat R c.pt := sorry

/-- The canonical filtered colimit of flat modules carries its reusable flatness instance. -/
@[stacks 05UT "canonical colimit instance"]
instance flatColimit [IsFiltered J] [HasColimit F] [∀ j, Module.Flat R (F.obj j)] :
    Module.Flat R
      (CategoryTheory.Limits.colimit F : ModuleCat.{max v u, u} R) := sorry

end ModuleCat.FilteredColimits
