/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Bounded.Homology
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Bounded Cohomology-In Object Properties

This leaf restricts `DerivedCategory.cohomologyIn P` along the canonical inclusions from the
bounded-below, bounded-above, and bounded derived categories.  Each specialization exposes the
same membership, degreewise projection, and monotonicity API.
-/

noncomputable section

universe w u v

open CategoryTheory

namespace CategoryTheory

open ObjectProperty

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- The cohomology-in owner on the bounded-below derived category. -/
@[stacks 06UQ "bounded-below cohomology-in property"]
abbrev DerivedCategory.Plus.cohomologyIn (P : ObjectProperty A) :
    ObjectProperty (DerivedCategory.Plus A) :=
  (DerivedCategory.cohomologyIn P).inverseImage DerivedCategory.Plus.ι

/-- The bounded-below derived full subcategory whose cohomology belongs to `P`. -/
@[stacks 06UQ "bounded-below cohomology-in full subcategory"]
abbrev DerivedCategory.Plus.CohomologyIn (P : ObjectProperty A) :=
  (DerivedCategory.Plus.cohomologyIn P).FullSubcategory

/-- The canonical inclusion of bounded-below derived objects with cohomology in `P` into the
ambient derived category. -/
@[stacks 0D6T "ambient inclusion of bounded-below cohomology-in objects"]
abbrev DerivedCategory.Plus.CohomologyIn.ambient (P : ObjectProperty A) :
    DerivedCategory.Plus.CohomologyIn P ⥤ DerivedCategory A :=
  (DerivedCategory.Plus.cohomologyIn P).ι ⋙ DerivedCategory.Plus.ι

/-- The cohomology-in owner on the bounded-above derived category. -/
@[stacks 06UQ "bounded-above cohomology-in property"]
abbrev DerivedCategory.Minus.cohomologyIn (P : ObjectProperty A) :
    ObjectProperty (DerivedCategory.Minus A) :=
  (DerivedCategory.cohomologyIn P).inverseImage DerivedCategory.Minus.ι

/-- The bounded-above derived full subcategory whose cohomology belongs to `P`. -/
@[stacks 06UQ "bounded-above cohomology-in full subcategory"]
abbrev DerivedCategory.Minus.CohomologyIn (P : ObjectProperty A) :=
  (DerivedCategory.Minus.cohomologyIn P).FullSubcategory

/-- The canonical inclusion of bounded-above derived objects with cohomology in `P` into the
ambient derived category. -/
@[stacks 06UQ "ambient inclusion of bounded-above cohomology-in objects"]
abbrev DerivedCategory.Minus.CohomologyIn.ambient (P : ObjectProperty A) :
    DerivedCategory.Minus.CohomologyIn P ⥤ DerivedCategory A :=
  (DerivedCategory.Minus.cohomologyIn P).ι ⋙ DerivedCategory.Minus.ι

/-- The cohomology-in owner on the bounded derived category. -/
@[stacks 06UQ "bounded cohomology-in property"]
abbrev DerivedCategory.Bounded.cohomologyIn (P : ObjectProperty A) :
    ObjectProperty (DerivedCategory.Bounded A) :=
  (DerivedCategory.cohomologyIn P).inverseImage DerivedCategory.Bounded.ι

/-- The bounded derived full subcategory whose cohomology belongs to `P`. -/
@[stacks 06UQ "bounded cohomology-in full subcategory"]
abbrev DerivedCategory.Bounded.CohomologyIn (P : ObjectProperty A) :=
  (DerivedCategory.Bounded.cohomologyIn P).FullSubcategory

/-- The canonical inclusion of bounded derived objects with cohomology in `P` into the ambient
derived category. -/
@[stacks 06UQ "ambient inclusion of bounded cohomology-in objects"]
abbrev DerivedCategory.Bounded.CohomologyIn.ambient (P : ObjectProperty A) :
    DerivedCategory.Bounded.CohomologyIn P ⥤ DerivedCategory A :=
  (DerivedCategory.Bounded.cohomologyIn P).ι ⋙ DerivedCategory.Bounded.ι

scoped[DerivedCategory.CohomologyIn] notation:max "D⁺[" P "]" =>
  DerivedCategory.Plus.CohomologyIn P

scoped[DerivedCategory.CohomologyIn] notation:max "D⁻[" P "]" =>
  DerivedCategory.Minus.CohomologyIn P

scoped[DerivedCategory.CohomologyIn] notation:max "Dᵇ[" P "]" =>
  DerivedCategory.Bounded.CohomologyIn P

namespace DerivedCategory.Plus.CohomologyIn

/-- Membership in the bounded-below cohomology-in property is degreewise membership in `P`. -/
@[simp, stacks 06UQ "bounded-below cohomology-in membership"]
theorem mem_iff (P : ObjectProperty A) (K : DerivedCategory.Plus A) :
    DerivedCategory.Plus.cohomologyIn P K ↔
      ∀ n : ℤ, P ((DerivedCategory.Plus.homologyFunctor A n).obj K) := sorry

/-- Every cohomology object of a bounded-below cohomology-in object belongs to `P`. -/
@[stacks 06UQ "bounded-below cohomology-in projection"]
theorem homology_mem (P : ObjectProperty A)
    (X : DerivedCategory.Plus.CohomologyIn P) (n : ℤ) :
    P ((DerivedCategory.Plus.homologyFunctor A n).obj X.obj) := sorry

/-- The bounded-below cohomology-in construction is monotone in the coefficient property. -/
@[stacks 06UQ "bounded-below cohomology-in monotonicity"]
theorem monotone {P Q : ObjectProperty A} (h : P ≤ Q) :
    DerivedCategory.Plus.cohomologyIn P ≤
      DerivedCategory.Plus.cohomologyIn Q := sorry

end DerivedCategory.Plus.CohomologyIn

namespace DerivedCategory.Minus.CohomologyIn

/-- Membership in the bounded-above cohomology-in property is degreewise membership in `P`. -/
@[simp, stacks 06UQ "bounded-above cohomology-in membership"]
theorem mem_iff (P : ObjectProperty A) (K : DerivedCategory.Minus A) :
    DerivedCategory.Minus.cohomologyIn P K ↔
      ∀ n : ℤ, P ((DerivedCategory.Minus.homologyFunctor A n).obj K) := sorry

/-- Every cohomology object of a bounded-above cohomology-in object belongs to `P`. -/
@[stacks 06UQ "bounded-above cohomology-in projection"]
theorem homology_mem (P : ObjectProperty A)
    (X : DerivedCategory.Minus.CohomologyIn P) (n : ℤ) :
    P ((DerivedCategory.Minus.homologyFunctor A n).obj X.obj) := sorry

/-- The bounded-above cohomology-in construction is monotone in the coefficient property. -/
@[stacks 06UQ "bounded-above cohomology-in monotonicity"]
theorem monotone {P Q : ObjectProperty A} (h : P ≤ Q) :
    DerivedCategory.Minus.cohomologyIn P ≤
      DerivedCategory.Minus.cohomologyIn Q := sorry

end DerivedCategory.Minus.CohomologyIn

namespace DerivedCategory.Bounded.CohomologyIn

/-- Membership in the bounded cohomology-in property is degreewise membership in `P`. -/
@[simp, stacks 06UQ "bounded cohomology-in membership"]
theorem mem_iff (P : ObjectProperty A) (K : DerivedCategory.Bounded A) :
    DerivedCategory.Bounded.cohomologyIn P K ↔
      ∀ n : ℤ, P ((DerivedCategory.Bounded.homologyFunctor A n).obj K) := sorry

/-- Every cohomology object of a bounded cohomology-in object belongs to `P`. -/
@[stacks 06UQ "bounded cohomology-in projection"]
theorem homology_mem (P : ObjectProperty A)
    (X : DerivedCategory.Bounded.CohomologyIn P) (n : ℤ) :
    P ((DerivedCategory.Bounded.homologyFunctor A n).obj X.obj) := sorry

/-- The bounded cohomology-in construction is monotone in the coefficient property. -/
@[stacks 06UQ "bounded cohomology-in monotonicity"]
theorem monotone {P Q : ObjectProperty A} (h : P ≤ Q) :
    DerivedCategory.Bounded.cohomologyIn P ≤
      DerivedCategory.Bounded.cohomologyIn Q := sorry

end DerivedCategory.Bounded.CohomologyIn

end CategoryTheory
