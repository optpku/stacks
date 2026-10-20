module

public import ReasLib.CategoryTheory.Sites.Simplicial.Total
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

variable {C : SimplexCategory ⥤ Cat.{v, u}} (J : ∀ n, Precoverage (C.obj n))
variable [SimplicialSites.IsSiteDiagram C J]

/- Lemma 85.3.1: let `C` be a simplicial object in the category of sites. With notation
as above we construct a site `C_total` as follows. An object of `C_total` is an object
`U` of `C.obj n` for some `n`, a morphism `(φ, f) : U ⟶ V` of `C_total` is given by a
map `φ : m ⟶ n` with `U` an object of `C.obj n`, `V` an object of `C.obj m` and a
morphism `f : U ⟶ u_φ(V)` of `C.obj n`, and a covering `{(id, f_i) : U_i ⟶ U}` in
`C_total` is given by an `n` and a covering `{f_i : U_i ⟶ U}` of `C.obj n`. -/
@[stacks 09WC] #check
  (CategoryTheory.SimplicialSites.precoverage.isSite C J :
    (CategoryTheory.SimplicialSites.precoverage C J).IsSite)

#check (SimplicialSites.ofObj C :
  ∀ n : SimplexCategory, C.obj n → SimplicialSites.totalSite C)
#check (SimplicialSites.homMk (C := C) :
  ∀ {U V : SimplicialSites.totalSite C}
    (φ : SimplicialSites.degree V ⟶ SimplicialSites.degree U),
    (SimplicialSites.obj U ⟶ (C.map φ).toFunctor.obj (SimplicialSites.obj V)) → (U ⟶ V))
#check (SimplicialSites.precoverage C J :
  Precoverage (SimplicialSites.totalSite C))
#check (SimplicialSites.topology C J :
  GrothendieckTopology (SimplicialSites.totalSite C))
