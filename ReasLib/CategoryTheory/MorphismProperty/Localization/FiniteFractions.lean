/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.Data.Finite.Defs

/-!
# Common denominators for finite families of fractions

Finite families of morphisms in a localization admit fraction representatives with one common
denominator.  The statements are independent of the chosen localization model and allow the
non-denominator objects to vary with the finite index.
-/

@[expose] public section

open CategoryTheory
open MorphismProperty

universe u v uι uD vD

namespace CategoryTheory.Localization

variable {C : Type u} {D : Type uD} [Category.{v} C] [Category.{vD} D]
variable (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]

/-- A finite family of localized morphisms with common target has left-fraction representatives
with one common denominator. -/
@[stacks 04VE "finite common left denominator"]
theorem exists_leftFraction_finite [W.HasLeftCalculusOfFractions]
    {ι : Type uι} [Finite ι] {X : ι → C} {Y : C}
    (g : ∀ i, L.obj (X i) ⟶ L.obj Y) :
    ∃ (Y' : C) (s : Y ⟶ Y') (hs : W s) (f : ∀ i, X i ⟶ Y'),
      ∀ i, g i = (LeftFraction.mk (f i) s hs).map L (inverts L W) := sorry

/-- A finite family of localized morphisms with common source has right-fraction representatives
with one common denominator. -/
@[stacks 04VI "finite common right denominator"]
theorem exists_rightFraction_finite [W.HasRightCalculusOfFractions]
    {ι : Type uι} [Finite ι] {X : C} {Y : ι → C}
    (g : ∀ i, L.obj X ⟶ L.obj (Y i)) :
    ∃ (X' : C) (s : X' ⟶ X) (hs : W s) (f : ∀ i, X' ⟶ Y i),
      ∀ i, g i = (RightFraction.mk s hs (f i)).map L (inverts L W) := sorry

end CategoryTheory.Localization
