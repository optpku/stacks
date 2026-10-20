module

public import ReasLib.CategoryTheory.Monoidal.Closed.Dualizable
public import ReasLib.CategoryTheory.Monoidal.Closed.LaxMonoidal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Internal Hom comparisons on dualizable objects

The internal-Hom comparison of a strong monoidal functor is invertible when its contravariant
argument is right-dualizable.  This is the generic mechanism behind pullback/internal-Hom
comparison theorems for perfect complexes.
-/

@[expose] public section

open CategoryTheory.MonoidalClosed

noncomputable section

universe u₁ v₁ u₂ v₂

namespace CategoryTheory.Functor.LaxMonoidal.InternalHom

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
variable (F : C ⥤ D) [F.Monoidal]

/-- A strong monoidal functor preserves the internal Hom out of a right-dualizable object. -/
@[stacks 0GM7 "generic dualizable criterion"]
theorem isIso_of_isRightDualizable {X : C} [Closed X] [Closed (F.obj X)]
    (hX : IsRightDualizable X) (Y : C) :
    IsIso (comparison F X Y) := sorry

end CategoryTheory.Functor.LaxMonoidal.InternalHom
