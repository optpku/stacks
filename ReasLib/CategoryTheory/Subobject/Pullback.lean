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
    (Subobject.pullback f).obj P = (⊤ : Subobject X) ↔ P = ⊤ := sorry

/-- The pullback of a proper subobject along an epimorphism is proper. -/
@[stacks 079J "pullback of a proper subobject"]
theorem pullback_ne_top_of_epi {X Y : C} (f : X ⟶ Y) [Epi f]
    {P : Subobject Y} (hP : P ≠ ⊤) :
    (Subobject.pullback f).obj P ≠ (⊤ : Subobject X) := sorry

end CategoryTheory.Subobject
