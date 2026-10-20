module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Restriction.Presentation

open CategoryTheory AlgebraicGeometry

universe u

/- The canonical arrow-space comparison realizes both fibre-product squares. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.pullbackArrowIso :
  {S : Scheme.{u}} → {B : AlgebraicSpace S} →
    (G : AlgebraicGeometry.GroupoidAlgebraicSpace B) →
      {U' : Over B} → (g : U' ⟶ G.U) →
        (G.toPreRelation.pullback g).left ≅ G.iteratedPullbackArrows g)
