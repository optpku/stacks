module

public import ReasLib.CategoryTheory.Sites.Grothendieck.Fiberwise

@[expose] public section

open CategoryTheory

universe u v

variable {F : SimplicialObject Cat.{v, u}} (J : ∀ n, Precoverage (F.obj n))

/- The identity-degree fiber precoverage on the Grothendieck construction and its
fiberwise site interface remain available through this chapter import. -/
#check (Grothendieck.precoverage F J : Precoverage (Grothendieck F))
