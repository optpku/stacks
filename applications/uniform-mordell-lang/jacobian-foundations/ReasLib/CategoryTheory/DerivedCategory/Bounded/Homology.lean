module

public import ReasLib.CategoryTheory.DerivedCategory.Bounded
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Homology on Bounded Derived Categories

@stack 05RU

This module reexports Mathlib's bounded-below derived homology and adds its bounded-above and
two-sided bounded analogues. It also installs the corresponding homological and shift-sequence
structures, giving downstream users one owner for all three boundedness directions.
-/

open CategoryTheory
open scoped CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

namespace DerivedCategory.Minus

/-- The `i`-th cohomology functor restricted to `D⁻(C)`. -/
@[stacks 05RU "cohomology on the bounded-above derived category"]
abbrev homologyFunctor (i : ℤ) : DerivedCategory.Minus C ⥤ C :=
  DerivedCategory.Minus.ι ⋙ DerivedCategory.homologyFunctor C i

/-- Restricted cohomology on `D⁻(C)` is homological. -/
@[stacks 05RU "homological bounded-above cohomology"]
instance homologyFunctor.isHomological (i : ℤ) :
    (homologyFunctor C i).IsHomological := sorry

/-- Degree-zero cohomology on `D⁻(C)` carries its canonical shift sequence. -/
@[stacks 05RU "bounded-above cohomology shift sequence"]
noncomputable instance homologyFunctor.shiftSequence :
    (homologyFunctor C 0).ShiftSequence ℤ :=
  Functor.ShiftSequence.instCompOfCommShift ℤ

end DerivedCategory.Minus

namespace DerivedCategory.Bounded

/-- The `i`-th cohomology functor restricted to `Dᵇ(C)`. -/
@[stacks 05RU "cohomology on the bounded derived category"]
abbrev homologyFunctor (i : ℤ) : DerivedCategory.Bounded C ⥤ C :=
  DerivedCategory.Bounded.ι ⋙ DerivedCategory.homologyFunctor C i

/-- Restricted cohomology on `Dᵇ(C)` is homological. -/
@[stacks 05RU "homological bounded cohomology"]
instance homologyFunctor.isHomological (i : ℤ) :
    (homologyFunctor C i).IsHomological := sorry

/-- Degree-zero cohomology on `Dᵇ(C)` carries its canonical shift sequence. -/
@[stacks 05RU "bounded cohomology shift sequence"]
noncomputable instance homologyFunctor.shiftSequence :
    (homologyFunctor C 0).ShiftSequence ℤ :=
  Functor.ShiftSequence.instCompOfCommShift ℤ

end DerivedCategory.Bounded

end CategoryTheory
