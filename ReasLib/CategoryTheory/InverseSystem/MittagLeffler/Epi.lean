module

public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler
public import ReasLib.CategoryTheory.Subobject.Image
import Mathlib.Tactic.CrossRefAttribute

/-!
# Epimorphic inverse systems are Mittag-Leffler

An inverse system whose transition maps are epimorphisms has constant full image at every
target stage.  This leaf packages that elementary criterion independently of modules and of a
particular quotient construction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.SequentialInverseSystem.IsMittagLeffler

variable {C : Type u} [Category.{v} C] [HasImages C]

/-- A sequential inverse system whose long transition maps are all epimorphisms is
Mittag-Leffler. -/
theorem of_epi_transitionMap
    (F : SequentialInverseSystem C)
    (hF : ∀ {i j : ℕ} (hij : i ≤ j), Epi (F.transitionMap hij)) :
    F.IsMittagLeffler := sorry

/-- Epimorphic successor transitions suffice for the Mittag-Leffler condition. -/
theorem of_epi_stepMap
    (F : SequentialInverseSystem C)
    (hF : ∀ n : ℕ, Epi (F.stepMap n)) :
    F.IsMittagLeffler := sorry

end CategoryTheory.SequentialInverseSystem.IsMittagLeffler
