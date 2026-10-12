/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
  letI : ∀ j, IsIso (f.app j) := fun j ↦ by
    change IsIso (((evaluation J C).obj j).map f)
    exact h j
  exact NatIso.isIso_of_isIso_app f

end CategoryTheory.FunctorCategory
