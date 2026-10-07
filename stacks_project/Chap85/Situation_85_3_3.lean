module

public import stacks_project.Chap85.Situation_85_3_3_Fiberwise
public import stacks_project.Chap85.Situation_85_3_3_MorphismDiagram
import StacksCheckRecall

/-!
# Situation 85.3.3

Working setup with two alternative presentations of a simplicial diagram of
sites: morphisms of sites (case A) or cocontinuous functors with property `P`
(case B), together with the named morphisms of topoi `f_φ` and the total site.
-/

@[expose] public section

open CategoryTheory

/- Situation 85.3.3 (1): case A, a covariant simplex diagram of morphisms of sites.
For `φ : m ⟶ n` the continuous functor `u_φ : C.obj m ⥤ C.obj n` presents a
morphism of sites `f_φ : C.obj n ⟶ C.obj m` and a morphism of topoi
`f_φ : Sh(C.obj n) ⟶ Sh(C.obj m)`; `C_total` is the total site of Lemma 85.3.1. -/
@[stacks 09WE] #check @SimplicialSites.IsMorphismDiagram
@[stacks 09WE] #check @SimplicialSites.toposMap
@[stacks 09WE] #check @SimplicialSites.totalSite
@[stacks 09WE] #check @SimplicialSites.precoverage
@[stacks 09WE] #check @SimplicialSites.topology

/- Situation 85.3.3 (2): case B, a simplicial object of sites whose structure maps
are cocontinuous functors with property `P`. For `φ : m ⟶ n` the functor
`u_φ : C_n ⥤ C_m` induces `f_φ : Sh(C_n) ⟶ Sh(C_m)`; `C_total` is the total site
of Lemma 85.3.2. -/
@[stacks 09WE] #check @Grothendieck.IsFiberwiseSite
@[stacks 09WE] #check @Grothendieck.toposMap
@[stacks 09WE] #check @Grothendieck.precoverage
@[stacks 09WE] #check @Grothendieck.topology
