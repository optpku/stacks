module

public import ReasLib.CategoryTheory.DerivedCategory.FunctorCategory.DerivedEvaluation.Map

@[expose] public section

/-!
# Naturality of Derived Evaluation Maps

The derived transformation induced by an indexing morphism is characterized
by compatibility with the two canonical evaluation units.
-/

open CategoryTheory

noncomputable section

universe wD wA vJ uJ vA uA

namespace CategoryTheory.FunctorCategory.DerivedEvaluation.derivedMap

variable (J : Type uJ) [Category.{vJ} J]
variable (A : Type uA) [Category.{vA} A] [Abelian A]
variable [HasDerivedCategory.{wA} A]
variable [HasDerivedCategory.{wD} (J ⥤ A)]

/-- A derived evaluation map is compatible with its source and target units. -/
theorem unit_fac {i j : J} (f : i ⟶ j) :
    unit J A i ≫
        Functor.whiskerLeft
          (DerivedCategory.Q :
            CochainComplex (J ⥤ A) ℤ ⥤ DerivedCategory (J ⥤ A))
          (derivedMap J A f) =
      cochainMap J A f ≫ unit J A j := sorry

/-- Component form of `unit_fac` at a cochain complex. -/
@[reassoc]
theorem unit_app {i j : J} (f : i ⟶ j) (K : CochainComplex (J ⥤ A) ℤ) :
    (unit J A i).app K ≫
        (derivedMap J A f).app
          ((DerivedCategory.Q :
            CochainComplex (J ⥤ A) ℤ ⥤ DerivedCategory (J ⥤ A)).obj K) =
      (cochainMap J A f).app K ≫ (unit J A j).app K := sorry

end CategoryTheory.FunctorCategory.DerivedEvaluation.derivedMap
