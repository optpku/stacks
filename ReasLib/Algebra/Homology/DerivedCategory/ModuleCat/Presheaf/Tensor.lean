/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Graded
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived tensor products of module-valued presheaves

The pointwise tensor product on `Cᵒᵖ ⥤ ModuleCat B` has canonical fixed-factor and two-variable
unbounded derived functors.  The chosen localization remains the ordinary explicit
`HasDerivedCategory` input; only the Prop-valued existence of the derived tensor models is
installed here.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe q v u w

namespace ModuleCat.Presheaf

variable {C : Type u} [Category.{v} C]
variable (B : Type w) [CommRing B]
variable [HasDerivedCategory.{q} (Presheaf C B)]

/-- Module-valued presheaves admit the canonical fixed-left and fixed-right unbounded derived
tensor functors. -/
@[stacks 06YU "module-presheaf derived tensor"]
instance hasDerivedTensor :
    DerivedCategory.DerivedTensor.Has (C := Presheaf C B) := sorry

/-- The pointwise tensor bifunctor on module-valued presheaves admits a canonical total left
derived bifunctor in both variables. -/
@[stacks 06YU "module-presheaf two-variable derived tensor"]
instance hasDerivedTensorBifunctor :
    DerivedCategory.DerivedTensor.Bifunctor.Has
      (C := Presheaf C B) := sorry

end ModuleCat.Presheaf
