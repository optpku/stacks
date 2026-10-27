/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Projective.Finite

/-! Compatibility checks for the finite filtered-projective API. -/

open CategoryTheory CategoryTheory.Limits

universe v u
variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasZeroMorphisms C]
  [HasCokernels C]

#check (CategoryTheory.FilteredObject.Finite.FilteredProjective.property C :
  ObjectProperty (CategoryTheory.FilteredObject.Finite.category C))
#check (CategoryTheory.FilteredObject.Finite.FilteredProjective.category C : Type (max u v))
