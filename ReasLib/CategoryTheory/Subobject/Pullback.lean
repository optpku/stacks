/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Balanced
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Pullback of Proper Subobjects

This module records how pullback along an epimorphism reflects the top subobject.  The result only
uses balancedness and pullbacks, so it is available well below the abelian setting of its original
application.
-/

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Subobject

variable {C : Type u} [Category.{v} C] [Balanced C] [HasPullbacks C]

/-- Pullback along an epimorphism reflects the top subobject. -/
@[stacks 079J "pullback reflects top"]
theorem pullback_eq_top_iff_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] (P : Subobject Y) :
    (Subobject.pullback f).obj P = (⊤ : Subobject X) ↔ P = ⊤ := by
  constructor
  · intro h
    have hf : P.Factors f := by
      simpa using (pullback_factors_iff f P (𝟙 X)).mp
        (h ▸ top_factors (𝟙 X))
    have hE : Epi P.arrow := epi_of_epi_fac (P.factorThru_arrow f hf)
    exact (isIso_arrow_iff_eq_top P).mp
      ((isIso_iff_mono_and_epi P.arrow).mpr ⟨inferInstance, hE⟩)
  · rintro rfl
    exact pullback_top f

/-- The pullback of a proper subobject along an epimorphism is proper. -/
@[stacks 079J "pullback of a proper subobject"]
theorem pullback_ne_top_of_epi {X Y : C} (f : X ⟶ Y) [Epi f]
    {P : Subobject Y} (hP : P ≠ ⊤) :
    (Subobject.pullback f).obj P ≠ (⊤ : Subobject X) :=
  fun h ↦ hP ((pullback_eq_top_iff_of_epi f P).mp h)

end CategoryTheory.Subobject
