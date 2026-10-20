/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Derived Objects with Cohomology in an Object Property

This leaf owns the object property on a derived category defined by a degreewise condition on
cohomology, its full subcategory, and the basic membership and monotonicity API.  Closure
properties and bounded specializations live in separate leaves.
-/

noncomputable section

universe w u v

open CategoryTheory

namespace CategoryTheory

open ObjectProperty

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- The object property on `DerivedCategory A` consisting of the objects whose
cohomology in every degree belongs to `P`. -/
@[stacks 06UQ "derived objects with cohomology in an object property"]
abbrev DerivedCategory.cohomologyIn (P : ObjectProperty A) :
    ObjectProperty (DerivedCategory A) :=
  fun K ↦ ∀ n : ℤ, P ((DerivedCategory.homologyFunctor A n).obj K)

namespace DerivedCategory

/-- The full subcategory of `DerivedCategory A` consisting of the objects whose
cohomology in every degree belongs to `P`. -/
@[stacks 06UQ "derived cohomology-in full subcategory"]
abbrev CohomologyIn (P : ObjectProperty A) :=
  (DerivedCategory.cohomologyIn P).FullSubcategory

end DerivedCategory

scoped[DerivedCategory.CohomologyIn] notation:max "D[" P "]" =>
  DerivedCategory.CohomologyIn P

namespace DerivedCategory.CohomologyIn

/-- Membership in the cohomology-in property is the degreewise cohomology condition. -/
@[simp, stacks 06UQ "cohomology-in membership"]
theorem mem_iff (P : ObjectProperty A) (K : DerivedCategory A) :
    DerivedCategory.cohomologyIn P K ↔
      ∀ n : ℤ, P ((DerivedCategory.homologyFunctor A n).obj K) := sorry

/-- Every cohomology object of an object of `DerivedCategory.CohomologyIn P` belongs to `P`. -/
@[stacks 06UQ "cohomology of a cohomology-in object"]
theorem homology_mem (P : ObjectProperty A)
    (X : DerivedCategory.CohomologyIn P) (n : ℤ) :
    P ((DerivedCategory.homologyFunctor A n).obj X.obj) := sorry

/-- Enlarging the coefficient object property enlarges the associated cohomology-in property. -/
@[stacks 06UQ "monotonicity of the cohomology-in construction"]
theorem monotone {P Q : ObjectProperty A} (h : P ≤ Q) :
    DerivedCategory.cohomologyIn P ≤ DerivedCategory.cohomologyIn Q := sorry

end DerivedCategory.CohomologyIn

end CategoryTheory
