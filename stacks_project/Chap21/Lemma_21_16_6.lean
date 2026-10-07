module

public import ReasLib.CategoryTheory.Sites.Cofiltered.StageFamily.Cohomology
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.16.6

The fixed-object cohomology diagrams and their finality comparison are owned by
`CofilteredSiteDiagram.StageFamily.Cohomology`; this chapter entry is the source-facing recall.
-/

/- Lemma 21.16.6 (09YP): for a compatible inverse system of abelian sheaves on a cofiltered
inverse system of sites, the filtered colimit over arrows `a : j ⟶ i` of
`H^p(u_a(X), 𝓕_j)` is canonically isomorphic to the cohomology of the colimit sheaf over
`u_i(X)`. -/
@[stacks 09YP]
#check @CategoryTheory.CofilteredSiteDiagram.StageFamily.Cohomology.colimit_isomorphic

#check @CategoryTheory.CofilteredSiteDiagram.StageFamily.Cohomology.objectCohomology
#check @CategoryTheory.CofilteredSiteDiagram.StageFamily.Cohomology.diagram
#check @CategoryTheory.CofilteredSiteDiagram.StageFamily.Cohomology.over
#check @CategoryTheory.CofilteredSiteDiagram.StageFamily.Cohomology.over_obj_iso
#check @CategoryTheory.CofilteredSiteDiagram.StageFamily.Cohomology.comparison
#check @CategoryTheory.CofilteredSiteDiagram.StageFamily.Cohomology.comparison_isIso

end
