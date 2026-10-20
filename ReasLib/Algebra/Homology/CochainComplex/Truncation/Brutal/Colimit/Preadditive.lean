/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Truncation.Brutal.Colimit.Comparison
public import ReasLib.Algebra.Homology.CochainComplex.Truncation.Brutal.Preadditive
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Colimit
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Additivity of the chosen brutal-truncation colimit

The chosen colimit of the functorial brutal-truncation diagram is additive
whenever the required sequential colimits exist.  This is a facade instance
over the generic colimit functor, so clients do not need a local `letI`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.CochainComplex.Brutal.Trunc.Colimit

variable {A : Type u} [Category.{v} A] [Abelian A]
variable [HasColimitsOfShape ℕ (CochainComplex A ℤ)]

/-- The chosen colimit of the brutal truncation diagram is additive. -/
@[stacks 0D8Z]
noncomputable instance functor_additive :
    (functor (A := A)).Additive := sorry

#synth (functor (A := A)).Additive

end CategoryTheory.CochainComplex.Brutal.Trunc.Colimit
