module

public import ReasLib.CategoryTheory.Semigroupal.Unit

@[expose] public section

universe v u

#check (CategoryTheory.SemigroupalCategory.UnitSeed.ofUnit :
  ∀ {C : Type u} [CategoryTheory.Category.{v} C] [CategoryTheory.SemigroupalCategory C],
    CategoryTheory.SemigroupalCategory.Unit C → CategoryTheory.SemigroupalCategory.UnitSeed C)
