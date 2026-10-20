/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import ReasLib.CategoryTheory.Preadditive.Limits

/-!
# Right Derived Sequential Limits

This leaf gives the ordinary nonnegative right-derived functors of sequential inverse limit a
stable `DerivedLimit` owner.  The Milnor cokernel model for degree one remains available as
`DerivedLimit.R1`; this API instead exposes the canonical injective-resolution functors in every
nonnegative degree.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory

namespace DerivedLimit

variable {A : Type u} [Category.{v} A] [Abelian A]
variable [HasLimitsOfShape ℕᵒᵖ A]
variable [HasInjectiveResolutions (SequentialInverseSystem A)]

/-- The `p`th ordinary right-derived functor of sequential inverse limit. -/
noncomputable abbrev rightDerived (p : ℕ) : SequentialInverseSystem A ⥤ A :=
  (lim : SequentialInverseSystem A ⥤ A).rightDerived p

end DerivedLimit

end CategoryTheory
