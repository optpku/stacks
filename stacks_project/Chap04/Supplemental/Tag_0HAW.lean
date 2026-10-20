module

public import ReasLib.CategoryTheory.Semigroupal.Unit
import StacksCheckRecall

@[expose] public section

universe v u

/- Lemma [Stacks 0HAW] In a category with a coherent tensor and no chosen unit,
units correspond bijectively to cancellable idempotents with specified multiplication. -/
@[stacks 0HAW] #check (CategoryTheory.SemigroupalCategory.unitEquiv :
  ∀ (C : Type u) [CategoryTheory.Category.{v} C] [CategoryTheory.SemigroupalCategory C],
    CategoryTheory.SemigroupalCategory.Unit C ≃ CategoryTheory.SemigroupalCategory.UnitSeed C)
