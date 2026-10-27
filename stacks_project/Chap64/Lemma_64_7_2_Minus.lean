/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.Projective

/-! Compatibility check for the filtered-projective derived model. -/

open CategoryTheory

universe v u
namespace CategoryTheory.FilteredObject.FiniteDerived
variable (C : Type u) [_root_.CategoryTheory.Category.{v} C] [Abelian C]
variable [HasDerivedCategory (GradedObject ℤ C)]
variable (h_inverts : AssociatedGraded.Inverts C)

#check (FilteredObject.FiniteDerived.Minus.FilteredProjective.functor C h_inverts :
  HomotopyCategory.Minus (FilteredObject.Finite.FilteredProjective.category C) ⥤
    FilteredObject.FiniteDerived.Minus.Category C h_inverts)

end CategoryTheory.FilteredObject.FiniteDerived
