module

public import ReasLib.CategoryTheory.Sites.Grothendieck.SimplicialTopos

@[expose] public section

universe u v

open CategoryTheory

#check (CategoryTheory.Grothendieck.IsFiberwiseSite :
  ∀ (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n)), Prop)
