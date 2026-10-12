/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Functor.Category
public import ReasLib.CategoryTheory.DerivedCategory.FunctorCategory.DerivedEvaluation.Functoriality

@[expose] public section

/-!
# The Diagram of Derived Evaluations

@stack 0CQD

Derived evaluation at every indexing object first assembles into a functor
valued in functors. Flipping that functor gives a functor from the derived
category of diagrams to diagrams in the derived category.
-/

open CategoryTheory

noncomputable section

universe wD wA vJ uJ vA uA

namespace CategoryTheory.FunctorCategory.DerivedEvaluation

variable (J : Type uJ) [Category.{vJ} J]
variable (A : Type uA) [Category.{vA} A] [Abelian A]
variable [HasDerivedCategory.{wA} A]
variable [HasDerivedCategory.{wD} (J ⥤ A)]

/-- The indexing-category family of derived evaluation functors. -/
@[stacks 0CQD]
noncomputable def familyFunctor :
    J ⥤ (DerivedCategory (J ⥤ A) ⥤ DerivedCategory A) where
  obj j := functor J A j
  map f := derivedMap J A f
  map_id := fun _ ↦ sorry
  map_comp := fun _ _ ↦ sorry

/-- The functor sending a derived diagram to its diagram of derived
evaluations. -/
@[stacks 0CQD]
noncomputable def diagramFunctor :
    DerivedCategory (J ⥤ A) ⥤ J ⥤ DerivedCategory A :=
  (familyFunctor J A).flip

end CategoryTheory.FunctorCategory.DerivedEvaluation
