module

public import ReasLib.CategoryTheory.Groupoid.InFunctors.Representability

universe u v

/- Representability of groupoids in functors by coyoneda presentations with an existing pushout. -/
#check (CategoryTheory.GroupoidInFunctors.IsRepresentable.{u, v} :
  {C : Type u} → [CategoryTheory.Category.{v} C] →
    CategoryTheory.GroupoidInFunctors.{u, v, v} C → Prop)
