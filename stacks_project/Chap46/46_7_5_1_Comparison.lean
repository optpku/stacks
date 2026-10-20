module

public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Comparison.Plus

@[expose] public section

universe w v u

open CategoryTheory
open CategoryTheory.ObjectProperty

#check (@CategoryTheory.DerivedCategory.Plus.CohomologyIn.Comparison.functor :
  {A : Type u} → [Category.{v} A] → [Abelian A] → [HasDerivedCategory.{w} A] →
    (P : ObjectProperty A) → [IsWeakSerreClass P] →
      [HasDerivedCategory.{w} P.FullSubcategory] →
        DerivedCategory.Plus P.FullSubcategory ⥤ DerivedCategory.Plus.CohomologyIn P)
