module

public import ReasLib.CategoryTheory.Sites.Simplicial.Slice

@[expose] public section

universe u v

open CategoryTheory

variable {C : Type u} [Category.{v} C] (U : SimplicialObject C)

#check (CategoryTheory.SimplicialObject.sliceTotalSite U : Type (max u v))
