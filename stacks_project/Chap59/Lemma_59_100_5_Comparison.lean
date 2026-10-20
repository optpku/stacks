module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.EtaleCohomology

@[expose] public section

universe u

/- The finite-morphism fppf–étale cohomology comparison on schemes. -/
#check (AlgebraicGeometry.Scheme.FppfEtale.comparisonSituation.{u} :
  CategoryTheory.GrothendieckTopology.TopologyComparison.Situation.{u + 1, u, u + 1, u + 1, u + 1}
    AlgebraicGeometry.Scheme.fppfTopology AlgebraicGeometry.Scheme.etaleTopology
    (@AlgebraicGeometry.IsFinite : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
    (fun X : AlgebraicGeometry.Scheme.{u} ↦ AlgebraicGeometry.Scheme.FppfEtale.essImageAb X))

end
