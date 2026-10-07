module

public import ReasLib.CategoryTheory.DerivedCategory.Bounded
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Definition
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import ReasLib.CategoryTheory.DerivedCategory.HomotopyLimit.Cohomology
import Mathlib.Tactic.CrossRefAttribute

/-!
# Coarse Upper Bounds for Sequential Homotopy Limits

Without a Mittag-Leffler condition, a sequential homotopy limit of objects in `D^{≤ b}` can
acquire cohomology in degree `b + 1`.  This file owns that general, presentation-independent
bound.  Sharper bounds with an explicit `R¹lim` hypothesis live in the `R1` leaf.
@stack 09AU
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe w v u

namespace CategoryTheory.HomotopyLimit.IsOf

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
variable [HasCountableProducts C] [HasExactLimitsOfShape (Discrete ℕ) C]
variable [HasLimitsOfShape ℕᵒᵖ C]
variable {Ksys : SequentialInverseSystem (DerivedCategory C)}
variable {K : DerivedCategory C}

/-- A homotopy limit of objects uniformly in `D^{≤ b}` belongs to `D^{≤ b + 1}`. -/
@[stacks 09AU "coarse upper bound for a sequential homotopy limit"]
theorem isLE_add_one (hK : HomotopyLimit.IsOf Ksys K) {b : ℤ}
    (h_bound : ∀ n : ℕ, (Ksys.obj (Opposite.op n)).IsLE b) :
    K.IsLE (b + 1) := sorry

/-- A uniform stagewise upper bound makes every sequential homotopy limit bounded above. -/
@[stacks 09AU "bounded-above sequential homotopy limit"]
theorem isBoundedAbove (hK : HomotopyLimit.IsOf Ksys K)
    (h_bound : ∃ b : ℤ, ∀ n : ℕ, (Ksys.obj (Opposite.op n)).IsLE b) :
    K.IsBoundedAbove := sorry

end CategoryTheory.HomotopyLimit.IsOf
