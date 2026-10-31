/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.FiniteInjective
public import ReasLib.CategoryTheory.Filtration.FiniteInjective.GradedPiece
public import ReasLib.CategoryTheory.Filtration.FinitePreadditive
public import ReasLib.CategoryTheory.Filtration.Map.Preadditive
public import ReasLib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Additive Extensions from Finite Filtered-Injective Objects

This module packages an additive filtered extension together with its associated-graded and
forgetful comparisons. The package is independent of any derived-category construction and can
be reused whenever a functor is first defined on finite filtered-injective objects.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

noncomputable section

namespace CategoryTheory.FilteredObject.Finite.FilteredInjective

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B] [Abelian A] [Abelian B]

/-- An additive filtered extension of `T : A ⥤+ B` from finite filtered-injective objects.
The associated-graded and forgetful comparisons are isomorphisms of functors, so downstream
constructions do not depend on a particular split presentation of a filtered-injective object. -/
@[stacks 05U0 "filtered extension datum"]
structure Extension (T : A ⥤+ B) where
  /-- The additive functor taking finite filtered-injective objects to finite filtered objects. -/
  functor : category A ⥤+ FilteredObject.Finite.category B
  /-- Taking the `p`-th graded piece of the extension agrees naturally with applying `T` to the
  original `p`-th graded piece. -/
  gradedIso : ∀ p : ℤ,
    functor.obj ⋙ FilteredObject.Finite.AssociatedGraded.functor B ⋙ GradedObject.eval p ≅
      inclusion A ⋙ FilteredObject.Finite.AssociatedGraded.functor A ⋙
        GradedObject.eval p ⋙ T.obj
  /-- Forgetting the resulting filtration recovers the restriction of the original functor. -/
  forgetIso :
    functor.obj ⋙ FilteredObject.Finite.Forget.functor B ≅
      forget A ⋙ T.obj

namespace Extension

/-- The canonical filtered extension attached to a left exact functor.

Applying `T.obj` to every finite filtration gives a functor on finite filtered objects; restricting
it along the inclusion of finite filtered-injective objects supplies the required source.  The
underlying additive functor is obtained from Mathlib's `AdditiveFunctor.ofLeftExact`, so this
construction does not choose an element of `nonempty`. -/
@[stacks 05U0 "canonical left-exact filtered extension"]
noncomputable def ofLeftExact (T : A ⥤ₗ B) :
    Extension ((AdditiveFunctor.ofLeftExact A B).obj T) where
  functor :=
    AdditiveFunctor.of
      ((inclusion A : category A ⥤ FilteredObject.Finite.category A) ⋙
        FilteredObject.Finite.mapFunctor T.obj)
  gradedIso := FilteredInjective.GradedPiece.natIso T.obj
  forgetIso := Iso.refl _

/-- Objectwise computation for the canonical left-exact filtered extension. -/
@[stacks 05U0 "canonical left-exact extension on objects", simp]
theorem ofLeftExact_obj (T : A ⥤ₗ B) (I : category A) :
    ((ofLeftExact T).functor.obj).obj I =
      (FilteredObject.Finite.mapFunctor T.obj).obj I.obj := sorry

/-- Morphismwise computation for the canonical left-exact filtered extension. -/
@[stacks 05U0 "canonical left-exact extension on morphisms", simp]
theorem ofLeftExact_map {I J : category A} (T : A ⥤ₗ B) (f : I ⟶ J) :
    ((ofLeftExact T).functor.obj).map f =
      (FilteredObject.Finite.mapFunctor T.obj).map f.hom := sorry

/-- Associated-graded computation for the canonical left-exact filtered extension. -/
@[stacks 05U0 "canonical left-exact extension on graded pieces", simp]
theorem ofLeftExact_gradedIso (T : A ⥤ₗ B) (p : ℤ) :
    (ofLeftExact T).gradedIso p = FilteredInjective.GradedPiece.natIso T.obj p := sorry

/-- Every additive functor admits an additive filtered extension on finite filtered-injective
objects. -/
@[stacks 05U0]
theorem nonempty (T : A ⥤+ B) : Nonempty (Extension T) := sorry

end Extension

end CategoryTheory.FilteredObject.Finite.FilteredInjective
