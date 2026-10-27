/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Evaluation functors reflect isomorphisms jointly

The family of evaluation functors on a functor category is jointly conservative.  This is a
generic functor-category fact, independent of any additive or homological structure.
-/

@[expose] public section

universe vJ uJ vC uC

namespace CategoryTheory.FunctorCategory

/-- The evaluation functors `J ⥤ C ⥤ C` jointly reflect isomorphisms. -/
theorem evaluation_jointlyReflectsIsomorphisms
    (J : Type uJ) [Category.{vJ} J] (C : Type uC) [Category.{vC} C] :
    JointlyReflectIsomorphisms ((evaluation J C).obj : J → (J ⥤ C) ⥤ C) := by
  refine ⟨fun f ↦ ?_⟩
  intro h
  exact @NatIso.isIso_of_isIso_app J _ C _ _ _ f h

end CategoryTheory.FunctorCategory
