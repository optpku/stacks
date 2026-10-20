/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.RepresentedHom.IsOf
import StacksCheckRecall

/-!
# Lemma 15.87.7

@stack 0CQX
-/

@[expose] public section

open CategoryTheory

/- Lemma 15.87.7 (Stacks 0CQX): applying `Hom(-, L)` to a sequential homotopy colimit gives the
Milnor short exact sequence from `R¹ lim Hom(K_n, L[-1])` to `lim Hom(K_n, L)`.  The reusable
statement is `HomotopyColimit.IsOf.homShortExact`. -/
@[stacks 0CQX]
#check @CategoryTheory.HomotopyColimit.IsOf.homShortExact

#check @CategoryTheory.HomotopyColimit.RepresentedHom.tower
#check @CategoryTheory.HomotopyColimit.RepresentedHom.shiftedTower
