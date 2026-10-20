/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable

/-!
# Terminal coforks of sheafified representables

The canonical maps from two sheafified representables to the terminal sheaf
form a cofork.  This concrete cofork is the source-side datum for global
sections/equalizer arguments.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u v

namespace CategoryTheory.GrothendieckTopology.SheafifiedRepresentable

variable {C : Type u} [Category.{v} C]

/-- The canonical map from a sheafified representable to the terminal sheaf
coequalizes the two maps induced by `a` and `b`. -/
theorem terminalCofork_condition
    (J : GrothendieckTopology C) [HasWeakSheafify J (Type (max u v))]
    {U V : C} (a b : V ⟶ U) :
    J.sheafifiedRepresentableMap a ≫
        (Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from
          (J.sheafifiedRepresentable U) =
      J.sheafifiedRepresentableMap b ≫
        (Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from
          (J.sheafifiedRepresentable U) := sorry

/-- The canonical cofork from `h[V]^# ⇉ h[U]^#` to the terminal sheaf. -/
noncomputable def terminalCofork
    (J : GrothendieckTopology C) [HasWeakSheafify J (Type (max u v))]
    {U V : C} (a b : V ⟶ U) :
    Cofork (J.sheafifiedRepresentableMap a) (J.sheafifiedRepresentableMap b) :=
  Cofork.ofπ
    ((Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from
      (J.sheafifiedRepresentable U))
    (terminalCofork_condition J a b)

end CategoryTheory.GrothendieckTopology.SheafifiedRepresentable
