module

public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler

/-!
# Tail Invariance of the Mittag-Leffler Condition

The Mittag-Leffler condition on a sequential inverse system is invariant under deleting any
finite initial segment.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory.SequentialInverseSystem

variable {A : Type u} [Category.{v} A] [HasImages A]

namespace IsMittagLeffler

/-- A tail of a Mittag-Leffler sequential inverse system is Mittag-Leffler. -/
theorem shift {F : SequentialInverseSystem A}
    (hF : F.IsMittagLeffler) (n : ℕ) :
    (F.shift n).IsMittagLeffler := sorry

/-- Deleting a finite initial segment preserves and reflects the Mittag-Leffler condition. -/
theorem shift_iff (F : SequentialInverseSystem A) (n : ℕ) :
    F.IsMittagLeffler ↔ (F.shift n).IsMittagLeffler := sorry

end IsMittagLeffler

end CategoryTheory.SequentialInverseSystem
