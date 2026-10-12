/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Object
public import Mathlib.CategoryTheory.GradedObject
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Graded Pieces of a Filtration

Given a decreasing filtration `F` on an object `A`, the *graded piece* at index `p` is
the cokernel of `F.succInclusion p`.

We also define the associated graded object as the `ℤ`-graded object whose `p`-th component is
`F.gradedPiece p`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory

namespace DecreasingFiltration

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasCokernels C] {A : C}

/-- The graded piece at index `p` is the cokernel of `F.succInclusion p`. -/
@[stacks 0121 "graded pieces of decreasing filtrations"]
noncomputable abbrev gradedPiece (F : DecreasingFiltration A) (p : ℤ) : C :=
  cokernel (F.succInclusion p)

end DecreasingFiltration

namespace FilteredObject

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasCokernels C]

/-- The graded piece of a filtered object at index `p`. -/
@[stacks 0121 "graded pieces of filtered objects"]
noncomputable abbrev gradedPiece (A : FilteredObject C) (p : ℤ) : C :=
  A.filtration.gradedPiece p

/-- The associated graded object of a filtered object, as a `ℤ`-graded object. -/
@[stacks 0121 "associated graded object"]
noncomputable def associatedGraded (A : FilteredObject C) : GradedObject ℤ C :=
  fun p ↦ A.gradedPiece p

end FilteredObject

end CategoryTheory
