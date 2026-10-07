module

public import stacks_project.Chap85.Lemma_85_3_1_Total
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
@[stacks 09WC] #check SimplicialSites.totalSite C
@[stacks 09WC] #check SimplicialSites.homEquiv
@[stacks 09WC] #check SimplicialSites.precoverage C J
@[stacks 09WC] #check SimplicialSites.precoverage.hasIsos C J
@[stacks 09WC] #check SimplicialSites.precoverage.hasPullbacks C J
@[stacks 09WC] #check SimplicialSites.precoverage.isStableUnderBind C J
@[stacks 09WC] #check SimplicialSites.precoverage.hasFactoringPullbacks C J
@[stacks 09WC] #check SimplicialSites.exists_ofStage_isPullback C J
