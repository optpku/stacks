/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Truncation.Brutal.Trunc
public import ReasLib.CategoryTheory.DerivedCategory.Colimit.Sequential.Transport
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived Colimit of the Brutal Truncation Diagram

This leaf contains only the passage from the ordinary brutal truncation
diagram to its homotopy-colimit statement in the derived category.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory.CochainComplex.Brutal.Trunc.Colimit.Derived

variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A]
  [HasColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ A]

/-- Stacks 0D8Z: the derived images of the brutal truncation stages have the
original complex as a sequential homotopy colimit. -/
@[stacks 0D8Z]
theorem isOf (K : CochainComplex A ℤ) :
    HomotopyColimit.IsOf (Trunc.diagram K ⋙ DerivedCategory.Q)
      (DerivedCategory.Q.obj K) := sorry

end CategoryTheory.CochainComplex.Brutal.Trunc.Colimit.Derived
