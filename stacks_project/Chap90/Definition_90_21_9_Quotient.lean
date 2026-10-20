module

public import ReasLib.CategoryTheory.Groupoid.Quotient

universe u v w

open CategoryTheory
open scoped BasedFunctor

#check (CategoryTheory.GroupoidInFunctors.quotientMorphism :
  ∀ {C : Type u} [Category.{v} C] (G : GroupoidInFunctors.{u, v, w} C),
    (Functor.ofTypeValued G.U).toBasedCategory ⥤ᵇ
      (CategoryTheory.GroupoidInFunctors.quotient G).toBasedCategory)
