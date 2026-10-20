module

public import ReasLib.CategoryTheory.Filtration.Complex.FiniteForget
public import ReasLib.CategoryTheory.Filtration.Complex.FiniteTriangulated
public import ReasLib.CategoryTheory.GradedObject.Homology
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Homological functors attached to finite filtered complexes

This leaf owns the standard homology functors obtained after associated graded, evaluation at a
grading degree, and forgetting the filtration.  It is independent of derived categories and
provides degree-zero specializations together with the shift-sequence instances expected by
homological downstream APIs.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open ComplexShape

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject

variable (C : Type u) [Category.{v} C] [Abelian C]

namespace Finite

namespace AssociatedGraded

/-- Degree-`n` homology after the finite associated-graded homotopy functor. -/
@[stacks 05S0 "finite filtered associated-graded homology"]
noncomputable def homology (n : ℤ) :
    HomotopyCategory (FilteredObject.Finite.category C) (up ℤ) ⥤ GradedObject ℤ C :=
  Finite.AssociatedGraded.homotopy C ⋙
    HomotopyCategory.homologyFunctor (GradedObject ℤ C) (up ℤ) n

/-- Every finite associated-graded homology functor is homological. -/
@[stacks 05S0 "finite filtered associated-graded homology"]
noncomputable instance Homology.isHomological (n : ℤ) :
    (homology C n).IsHomological := sorry

namespace Homology

/-- Degree-zero homology after finite associated graded. -/
@[stacks 05S0 "finite filtered associated-graded degree-zero homology"]
noncomputable abbrev zero :=
  homology C 0

namespace Zero

/-- The canonical shift sequence whose degree-`n` term is finite associated-graded homology in
degree `n`. -/
@[stacks 05S0 "finite filtered associated-graded degree-zero homology"]
noncomputable instance shiftSequence :
    (zero C).ShiftSequence ℤ :=
  inferInstanceAs
    ((Finite.AssociatedGraded.homotopy C ⋙
      HomotopyCategory.homologyFunctor (GradedObject ℤ C) (up ℤ) 0).ShiftSequence ℤ)

/-- The `n`-th term of the finite associated-graded degree-zero shift sequence is the standard
degree-`n` homology functor. -/
@[stacks 05S0 "finite filtered associated-graded homology", simp]
theorem shift (n : ℤ) :
    (zero C).shift n = homology C n := sorry

end Zero

end Homology

end AssociatedGraded

namespace GradedPiece

/-- Degree-`n` homology after the `p`-th associated-graded piece. -/
@[stacks 05S0 "finite filtered graded-piece homology"]
noncomputable def homology (p n : ℤ) :
    HomotopyCategory (FilteredObject.Finite.category C) (up ℤ) ⥤ C :=
  Finite.AssociatedGraded.homotopy C ⋙
    (GradedObject.eval p).mapHomotopyCategory (up ℤ) ⋙
    HomotopyCategory.homologyFunctor C (up ℤ) n

/-- Every finite graded-piece homology functor is homological. -/
@[stacks 05S0 "finite filtered graded-piece homology"]
noncomputable instance Homology.isHomological (p n : ℤ) :
    (homology C p n).IsHomological := sorry

namespace Homology

/-- Degree-zero homology after the `p`-th associated-graded piece. -/
@[stacks 05S0 "finite filtered graded-piece degree-zero homology"]
noncomputable abbrev zero (p : ℤ) :=
  homology C p 0

namespace Zero

/-- The canonical shift sequence whose degree-`n` term is homology in degree `n` of the
`p`-th associated-graded piece. -/
@[stacks 05S0 "finite filtered graded-piece degree-zero homology"]
noncomputable instance shiftSequence (p : ℤ) :
    (zero C p).ShiftSequence ℤ :=
  inferInstanceAs
    ((Finite.AssociatedGraded.homotopy C ⋙
      (GradedObject.eval p).mapHomotopyCategory (up ℤ) ⋙
      HomotopyCategory.homologyFunctor C (up ℤ) 0).ShiftSequence ℤ)

/-- The `n`-th term of the degree-zero shift sequence for the `p`-th associated-graded piece is
the standard degree-`n` homology functor. -/
@[stacks 05S0 "finite filtered graded-piece homology", simp]
theorem shift (p n : ℤ) :
    (zero C p).shift n = homology C p n := sorry

end Zero

end Homology

end GradedPiece

namespace Forget

/-- Degree-`n` homology after forgetting a finite filtration. -/
@[stacks 05S0 "finite filtered forgetful homology"]
noncomputable def homology (n : ℤ) :
    HomotopyCategory (FilteredObject.Finite.category C) (up ℤ) ⥤ C :=
  Finite.Forget.homotopy C ⋙ HomotopyCategory.homologyFunctor C (up ℤ) n

/-- Every finite filtered forgetful homology functor is homological. -/
@[stacks 05S0 "finite filtered forgetful homology"]
noncomputable instance Homology.isHomological (n : ℤ) :
    (homology C n).IsHomological := sorry

namespace Homology

/-- Degree-zero homology after forgetting a finite filtration. -/
@[stacks 05S0 "finite filtered forgetful degree-zero homology"]
noncomputable abbrev zero :=
  homology C 0

namespace Zero

/-- The canonical shift sequence whose degree-`n` term is homology in degree `n` after
forgetting the finite filtration. -/
@[stacks 05S0 "finite filtered forgetful degree-zero homology"]
noncomputable instance shiftSequence :
    (zero C).ShiftSequence ℤ :=
  inferInstanceAs
    ((Finite.Forget.homotopy C ⋙
      HomotopyCategory.homologyFunctor C (up ℤ) 0).ShiftSequence ℤ)

/-- The `n`-th term of the finite forgetful degree-zero shift sequence is the standard
degree-`n` homology functor. -/
@[stacks 05S0 "finite filtered forgetful homology", simp]
theorem shift (n : ℤ) :
    (zero C).shift n = homology C n := sorry

end Zero

end Homology

end Forget

end Finite

end CategoryTheory.FilteredObject
