/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Projective

/-!
# Filtered Projective Objects

Filtered projectivity means projectivity of every associated graded piece in the ambient
category.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasCokernels C]

/- Filtered projective objects have projective associated graded pieces. -/
#check (CategoryTheory.FilteredObject.IsFilteredProjective : CategoryTheory.FilteredObject C → Prop)
