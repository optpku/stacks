module

public import ReasLib.CategoryTheory.Sites.Simplicial.Total

@[expose] public section

open CategoryTheory

universe u v

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))

#check (SimplicialSites.topology C J :
  GrothendieckTopology (SimplicialSites.totalSite C))
