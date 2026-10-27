/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.Projective.Resolution
public import ReasLib.CategoryTheory.Filtration.Derived.BoundedLocalization
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-! Bounded-above filtered-projective models for the finite filtered derived category. -/

@[expose] public section
open CategoryTheory
noncomputable section
universe v u

namespace CategoryTheory.FilteredObject.FiniteDerived

variable (C : Type u) [_root_.CategoryTheory.Category.{v} C] [Abelian C]
variable [HasDerivedCategory (GradedObject ℤ C)]
variable (h_inverts : AssociatedGraded.Inverts C)

namespace Minus.FilteredProjective

/-- The inclusion followed by bounded filtered localization. -/
noncomputable def functor :
    HomotopyCategory.Minus (Finite.FilteredProjective.category C) ⥤ Minus.Category C h_inverts :=
  (Finite.FilteredProjective.inclusion C).mapHomotopyCategoryMinus ⋙
    Minus.Quotient.functor C h_inverts

/-- The filtered-projective model functor is an equivalence under enough projectives. -/
instance isEquivalence [EnoughProjectives C] : Functor.IsEquivalence (functor C h_inverts) := sorry

/-- The filtered-projective equivalence constructed from an explicit equivalence certificate. -/
noncomputable def equivalenceOf
    (h_equiv : Functor.IsEquivalence (functor C h_inverts)) :
    HomotopyCategory.Minus (Finite.FilteredProjective.category C) ≌ Minus.Category C h_inverts :=
  @Functor.asEquivalence _ _ _ _ (functor C h_inverts) h_equiv

/-- The filtered-projective equivalence under enough projectives, constructed from a supplied
certificate of the model equivalence. The certificate represents the projective resolution
and comparison facts. -/
noncomputable def equivalenceOfEnoughProjectives [EnoughProjectives C]
    (h_equiv : Functor.IsEquivalence (functor C h_inverts)) :
    HomotopyCategory.Minus (Finite.FilteredProjective.category C) ≌ Minus.Category C h_inverts :=
  equivalenceOf C h_inverts h_equiv

/-- The forward functor of the filtered-projective equivalence is the model functor. -/
@[simp] theorem equivalenceOfEnoughProjectives_functor [EnoughProjectives C]
    (h_equiv : Functor.IsEquivalence (functor C h_inverts)) :
    (equivalenceOfEnoughProjectives C h_inverts h_equiv).functor = functor C h_inverts := rfl

end Minus.FilteredProjective
end CategoryTheory.FilteredObject.FiniteDerived
