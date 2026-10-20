module

public import ReasLib.CategoryTheory.Groupoid.InFunctors

universe u v w

/- Groupoids in set-valued functors, with their existing public operations and laws. -/
#check (CategoryTheory.GroupoidInFunctors.{u, v, w} :
  (C : Type u) → [CategoryTheory.Category.{v} C] → Type (max u v (w + 1)))
