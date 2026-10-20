module

public import ReasLib.CategoryTheory.DerivedCategory.Countable
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe w v u

/- Lemma 57.17.2 -/
@[stacks 0G0V]
#check
  (CategoryTheory.countableCategory_boundedDerived :
    ∀ (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
      [CountableCategory (Skeleton A)],
      CountableCategory (Skeleton (DerivedCategory.Bounded A)))
