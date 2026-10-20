/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Isomorphisms, Zero Objects, and Shifts for Cohomology-In Properties

The degreewise cohomology condition is invariant under derived isomorphisms and shifts, and it
contains zero as soon as the coefficient property does.  These facts require only the matching
structural assumptions on the coefficient property, not a weak Serre hypothesis.
-/

noncomputable section

open scoped CategoryTheory ZeroObject

universe w u v

open CategoryTheory

namespace CategoryTheory

open Limits ObjectProperty

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

namespace DerivedCategory.CohomologyIn

/-- Degreewise cohomology membership is invariant under isomorphisms when the coefficient
property is. -/
@[stacks 06UQ "isomorphism invariance of cohomology-in objects"]
instance closedUnderIso (P : ObjectProperty A) [P.IsClosedUnderIsomorphisms] :
    (DerivedCategory.cohomologyIn P).IsClosedUnderIsomorphisms := sorry

/-- The cohomology-in property contains a zero object whenever the coefficient property does. -/
@[stacks 06UQ "zero object in a cohomology-in subcategory"]
instance containsZero (P : ObjectProperty A) [P.ContainsZero]
    [P.IsClosedUnderIsomorphisms] :
    (DerivedCategory.cohomologyIn P).ContainsZero := sorry

/-- The cohomology-in property is stable under every integral shift. -/
@[stacks 06UQ "shift stability of cohomology-in objects"]
instance stableUnderShift (P : ObjectProperty A) [P.IsClosedUnderIsomorphisms] :
    (DerivedCategory.cohomologyIn P).IsStableUnderShift ℤ := sorry

/-- The zero derived object has cohomology in `P` whenever `P` contains zero. -/
@[stacks 06UQ "zero cohomology-in object"]
theorem zero_mem (P : ObjectProperty A) [P.ContainsZero]
    [P.IsClosedUnderIsomorphisms] :
    DerivedCategory.cohomologyIn P (0 : DerivedCategory A) := sorry

/-- Integral shifts preserve and reflect the property of having cohomology in `P`. -/
@[simp, stacks 06UQ "cohomology-in membership after a shift"]
theorem shift_iff (P : ObjectProperty A) [P.IsClosedUnderIsomorphisms]
    (K : DerivedCategory A) (n : ℤ) :
    DerivedCategory.cohomologyIn P (K⟦n⟧) ↔
      DerivedCategory.cohomologyIn P K := sorry

end DerivedCategory.CohomologyIn

namespace DerivedCategory.Plus.CohomologyIn

/-- The zero bounded-below derived object has cohomology in `P`. -/
@[simp, stacks 06UQ "zero bounded-below cohomology-in object"]
theorem zero_mem (P : ObjectProperty A) [P.ContainsZero]
    [P.IsClosedUnderIsomorphisms] :
    DerivedCategory.Plus.cohomologyIn P (0 : DerivedCategory.Plus A) := sorry

/-- Integral shifts preserve and reflect bounded-below cohomology-in membership. -/
@[simp, stacks 06UQ "bounded-below cohomology-in membership after a shift"]
theorem shift_iff (P : ObjectProperty A) [P.IsClosedUnderIsomorphisms]
    (K : DerivedCategory.Plus A) (n : ℤ) :
    DerivedCategory.Plus.cohomologyIn P (K⟦n⟧) ↔
      DerivedCategory.Plus.cohomologyIn P K := sorry

end DerivedCategory.Plus.CohomologyIn

namespace DerivedCategory.Minus.CohomologyIn

/-- The zero bounded-above derived object has cohomology in `P`. -/
@[simp, stacks 06UQ "zero bounded-above cohomology-in object"]
theorem zero_mem (P : ObjectProperty A) [P.ContainsZero]
    [P.IsClosedUnderIsomorphisms] :
    DerivedCategory.Minus.cohomologyIn P (0 : DerivedCategory.Minus A) := sorry

/-- Integral shifts preserve and reflect bounded-above cohomology-in membership. -/
@[simp, stacks 06UQ "bounded-above cohomology-in membership after a shift"]
theorem shift_iff (P : ObjectProperty A) [P.IsClosedUnderIsomorphisms]
    (K : DerivedCategory.Minus A) (n : ℤ) :
    DerivedCategory.Minus.cohomologyIn P (K⟦n⟧) ↔
      DerivedCategory.Minus.cohomologyIn P K := sorry

end DerivedCategory.Minus.CohomologyIn

namespace DerivedCategory.Bounded.CohomologyIn

/-- The zero bounded derived object has cohomology in `P`. -/
@[simp, stacks 06UQ "zero bounded cohomology-in object"]
theorem zero_mem (P : ObjectProperty A) [P.ContainsZero]
    [P.IsClosedUnderIsomorphisms] :
    DerivedCategory.Bounded.cohomologyIn P (0 : DerivedCategory.Bounded A) := sorry

/-- Integral shifts preserve and reflect bounded cohomology-in membership. -/
@[simp, stacks 06UQ "bounded cohomology-in membership after a shift"]
theorem shift_iff (P : ObjectProperty A) [P.IsClosedUnderIsomorphisms]
    (K : DerivedCategory.Bounded A) (n : ℤ) :
    DerivedCategory.Bounded.cohomologyIn P (K⟦n⟧) ↔
      DerivedCategory.Bounded.cohomologyIn P K := sorry

end DerivedCategory.Bounded.CohomologyIn

section

variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]

#synth (DerivedCategory.Plus.cohomologyIn P).IsClosedUnderIsomorphisms
#synth (DerivedCategory.Plus.cohomologyIn P).ContainsZero
#synth (DerivedCategory.Plus.cohomologyIn P).IsStableUnderShift ℤ
#synth (DerivedCategory.Minus.cohomologyIn P).IsClosedUnderIsomorphisms
#synth (DerivedCategory.Minus.cohomologyIn P).ContainsZero
#synth (DerivedCategory.Minus.cohomologyIn P).IsStableUnderShift ℤ
#synth (DerivedCategory.Bounded.cohomologyIn P).IsClosedUnderIsomorphisms
#synth (DerivedCategory.Bounded.cohomologyIn P).ContainsZero
#synth (DerivedCategory.Bounded.cohomologyIn P).IsStableUnderShift ℤ

end

end CategoryTheory
