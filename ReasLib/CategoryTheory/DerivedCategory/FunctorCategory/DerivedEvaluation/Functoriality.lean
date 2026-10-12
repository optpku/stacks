/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.FunctorCategory.DerivedEvaluation.Map

@[expose] public section

/-!
# Functoriality of Derived Evaluation Maps

Indexing morphisms act functorially on evaluation at the cochain and derived
levels. Underived functoriality is already the standard `Functor.map_id` and
`Functor.map_comp` API.
-/

open CategoryTheory

noncomputable section

universe wD wA vJ uJ vA uA

namespace CategoryTheory.FunctorCategory.DerivedEvaluation

namespace cochainMap

variable (J : Type uJ) [Category.{vJ} J]
variable (A : Type uA) [Category.{vA} A] [Abelian A]
variable [HasDerivedCategory.{wA} A]

/-- Identity indexing morphisms induce identity cochain transformations. -/
@[simp]
theorem id (i : J) :
    cochainMap J A (𝟙 i) = 𝟙 (cochainFunctor J A i) := sorry

/-- Cochain evaluation transformations preserve composition. -/
theorem comp {i j k : J} (f : i ⟶ j) (g : j ⟶ k) :
    cochainMap J A (f ≫ g) =
      cochainMap J A f ≫ cochainMap J A g := sorry

end cochainMap

namespace derivedMap

variable (J : Type uJ) [Category.{vJ} J]
variable (A : Type uA) [Category.{vA} A] [Abelian A]
variable [HasDerivedCategory.{wA} A]
variable [HasDerivedCategory.{wD} (J ⥤ A)]

/-- Identity indexing morphisms induce identity derived transformations. -/
@[simp]
theorem id (i : J) :
    derivedMap J A (𝟙 i) = 𝟙 (functor J A i) := sorry

/-- Derived evaluation transformations preserve composition. -/
theorem comp {i j k : J} (f : i ⟶ j) (g : j ⟶ k) :
    derivedMap J A (f ≫ g) =
      derivedMap J A f ≫ derivedMap J A g := sorry

end derivedMap

end CategoryTheory.FunctorCategory.DerivedEvaluation
