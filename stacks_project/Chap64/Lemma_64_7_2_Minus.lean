/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap64.Lemma_64_7_2_Projective
public import ReasLib.CategoryTheory.Filtration.Derived.BoundedLocalization
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# Filtered-Projective Models for Bounded-Above Finite Filtered Derived Categories

The functor in this file has the actual bounded-above homotopy category of
finite filtered-projective objects as its source.  It is a composite through
the finite filtered homotopy category and its canonical bounded localization;
it does not choose a derived-category presentation.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory

namespace FilteredObject

namespace FiniteDerived

variable (C : Type u) [_root_.CategoryTheory.Category.{v} C] [Abelian C]
variable [HasDerivedCategory (GradedObject ℤ C)]
variable (h_inverts : AssociatedGraded.Inverts C)

namespace Minus.FilteredProjective

/-- The canonical functor from bounded-above complexes of finite
filtered-projective objects to the bounded-above finite filtered derived
category. -/
noncomputable def functor :
    HomotopyCategory.Minus (Finite.FilteredProjective.category C) ⥤ Minus.Category C h_inverts :=
  (Finite.FilteredProjective.inclusion C).mapHomotopyCategoryMinus ⋙
    Minus.Quotient.functor C h_inverts

/-- The proposition that the filtered-projective model functor is an equivalence. -/
abbrev IsEquivalence : Prop := Functor.IsEquivalence (functor C h_inverts)

/-- Bounded-above complexes of finite filtered-projective objects compute the bounded-above
finite filtered derived category. -/
instance isEquivalence [EnoughProjectives C] : IsEquivalence C h_inverts := sorry

/-- A named inverse-equivalence package for the filtered-projective model of the
bounded-above finite filtered derived category, constructed from an explicit equivalence
certificate. -/
noncomputable def equivalenceOf (h_equiv : IsEquivalence C h_inverts) :
    HomotopyCategory.Minus (Finite.FilteredProjective.category C) ≌ Minus.Category C h_inverts :=
  @Functor.asEquivalence _ _ _ _ _
    h_equiv

/-- The canonical filtered-projective equivalence under enough projectives.

This is the reusable data owner for the standard model; callers should use it instead of
reconstructing an `IsEquivalence` proof merely to feed `equivalenceOf`. -/
noncomputable def equivalenceOfEnoughProjectives [EnoughProjectives C] :
    HomotopyCategory.Minus (Finite.FilteredProjective.category C) ≌ Minus.Category C h_inverts :=
  equivalenceOf C h_inverts (isEquivalence C h_inverts)

/-- The forward functor of the canonical filtered-projective equivalence. -/
@[simp]
theorem equivalenceOfEnoughProjectives_functor [EnoughProjectives C] :
    (equivalenceOfEnoughProjectives C h_inverts).functor = functor C h_inverts := sorry

/-- The inverse functor of the canonical filtered-projective equivalence is the inverse selected
by the canonical equivalence package. -/
theorem equivalenceOfEnoughProjectives_inverse [EnoughProjectives C] :
    (equivalenceOfEnoughProjectives C h_inverts).inverse =
      (equivalenceOf C h_inverts (isEquivalence C h_inverts)).inverse := sorry

end Minus.FilteredProjective

end FiniteDerived

end FilteredObject

end CategoryTheory
