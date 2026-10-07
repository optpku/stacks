module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced.Neighborhood
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory

/- Lemma 33.6.9: a locally Noetherian scheme over a field that is geometrically
reduced at a point has a geometrically reduced open neighborhood of that point. -/
@[stacks 0360] #check
  (AlgebraicGeometry.SchemeOverField.existsOpenNeighborhood_geometricallyReduced_of_geometricallyReducedAt :
    ∀ {k : Type u} [Field k]
      (X : Over (AlgebraicGeometry.Spec (CommRingCat.of k)))
      [AlgebraicGeometry.IsLocallyNoetherian X.left] (x : X.left),
      AlgebraicGeometry.SchemeOverField.geometricallyReducedAt X x →
        ∃ U : X.left.Opens, x ∈ U ∧
          AlgebraicGeometry.SchemeOverField.geometricallyReduced
            (Over.mk (U.ι ≫ X.hom)))
