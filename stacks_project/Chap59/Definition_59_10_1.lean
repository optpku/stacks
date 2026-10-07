module

public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Over
import StacksCheckRecall

universe w v u

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/- Definition 59.10.1: a formal coproduct of slice objects stores the arbitrary
index type and every source object and arrow, including the empty family. -/
@[stacks 03NG] #check (CategoryTheory.Limits.FormalCoproduct.ofArrows :
  {target : C} → {ι : Type w} → (objects : ι → C) →
    ((index : ι) → objects index ⟶ target) →
      CategoryTheory.Limits.FormalCoproduct.{w} (CategoryTheory.Over target))
