/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Colimit.Sequential
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Transporting Sequential Derived Homotopy Colimits

This leaf transports the canonical termwise-colimit presentation along an
isomorphism of cone objects.  The intrinsic homotopy-colimit predicate retains
its explicit coproduct cocone, so no auxiliary coproduct instance is exposed.
-/

open CategoryTheory.Limits
open scoped CategoryTheory.Limits.CountableFromSequential

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory.SequentialColimit

variable {A : Type u} [Category.{v} A] [Abelian A]
variable [HasDerivedCategory.{w} A]
variable [HasColimitsOfShape ℕ A]

/-- Stacks 0D8Z: if the derived image of a termwise sequential colimit is isomorphic to `X`,
then `X` is a homotopy colimit of the derived image sequence. -/
@[stacks 0D8Z]
theorem isOf_of_iso [HasExactColimitsOfShape ℕ A]
    (S : ℕ ⥤ CochainComplex A ℤ) {X : DerivedCategory A}
    (e : DerivedCategory.Q.obj (colimit S) ≅ X) :
    HomotopyColimit.IsOf (S ⋙ DerivedCategory.Q) X := sorry

end CategoryTheory.DerivedCategory.SequentialColimit
