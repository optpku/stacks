module

public import ReasLib.CategoryTheory.DerivedCategory.FunctorCategory.DerivedEvaluation.Diagram

@[expose] public section

/-!
# Computation Rules for the Diagram of Derived Evaluations

These rules expose the objects, indexing maps, and natural-transformation
components of `diagramFunctor` without unfolding its structure fields.
-/

open CategoryTheory

noncomputable section

universe wD wA vJ uJ vA uA

namespace CategoryTheory.FunctorCategory.DerivedEvaluation

variable (J : Type uJ) [Category.{vJ} J]
variable (A : Type uA) [Category.{vA} A] [Abelian A]
variable [HasDerivedCategory.{wA} A]
variable [HasDerivedCategory.{wD} (J ⥤ A)]

namespace familyFunctor

/-- Objectwise computation of the family of derived evaluation functors. -/
@[simp]
theorem obj (j : J) :
    (familyFunctor J A).obj j = functor J A j := sorry

/-- Morphism computation in the family of derived evaluation functors. -/
@[simp]
theorem map {i j : J} (f : i ⟶ j) :
    (familyFunctor J A).map f = derivedMap J A f := sorry

end familyFunctor

namespace diagramFunctor

/-- Objectwise computation of the derived-evaluation diagram. -/
@[simp]
theorem obj_obj (K : DerivedCategory (J ⥤ A)) (j : J) :
    ((diagramFunctor J A).obj K).obj j = (functor J A j).obj K := sorry

/-- An indexing morphism acts through the corresponding derived evaluation map. -/
@[simp]
theorem obj_map (K : DerivedCategory (J ⥤ A)) {i j : J} (f : i ⟶ j) :
    ((diagramFunctor J A).obj K).map f = (derivedMap J A f).app K := sorry

/-- Componentwise computation of the image of a derived-diagram morphism. -/
@[simp]
theorem map_app {K L : DerivedCategory (J ⥤ A)} (f : K ⟶ L) (j : J) :
    ((diagramFunctor J A).map f).app j = (functor J A j).map f := sorry

/-- The image of a derived-diagram morphism is natural in every indexing
morphism. -/
@[reassoc]
theorem map_naturality {K L : DerivedCategory (J ⥤ A)} (f : K ⟶ L)
    {i j : J} (g : i ⟶ j) :
    (derivedMap J A g).app K ≫ (functor J A j).map f =
      (functor J A i).map f ≫ (derivedMap J A g).app L := sorry

end diagramFunctor

end CategoryTheory.FunctorCategory.DerivedEvaluation
