module

public import ReasLib.CategoryTheory.Groupoid.InFunctors.Restriction

open CategoryTheory

universe u u' v v' w

/- Restriction of groupoids in set-valued functors along an arbitrary functor. -/
#check (CategoryTheory.GroupoidInFunctors.restrict.{u, u', v, v', w} :
  {C : Type u} → [CategoryTheory.Category.{v} C] →
  {C' : Type u'} → [CategoryTheory.Category.{v'} C'] →
  [CategoryTheory.Limits.HasPullbacks (C' ⥤ Type w)] →
  CategoryTheory.GroupoidInFunctors.{u, v, w} C → (C' ⥤ C) →
  CategoryTheory.GroupoidInFunctors.{u', v', w} C')
