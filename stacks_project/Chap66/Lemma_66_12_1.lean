module

import StacksCheckRecall

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Immersion
public import stacks_project.Chap66.Lemma_66_5_5_PointsTopology

/-!
# Immersions induce embeddings of points

An immersion of algebraic spaces over a scheme induces a topological embedding of
underlying point spaces onto a locally closed subset.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Topology

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 66.12.1 (1): an immersion induces a homeomorphism onto its image. -/
@[stacks 0ABJ] #check
  (AlgebraicGeometry.AlgebraicSpace.IsImmersion.isEmbedding_points :
    ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (f : Z ⟶ X) [IsImmersion f],
      Topology.IsEmbedding (Points.map f))

/- Lemma 66.12.1 (2): the image of an immersion on points is locally closed. -/
@[stacks 0ABJ] #check
  (AlgebraicGeometry.AlgebraicSpace.IsImmersion.isLocallyClosed_range_points :
    ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (f : Z ⟶ X) [IsImmersion f],
      IsLocallyClosed (Set.range (Points.map f)))

end AlgebraicGeometry.AlgebraicSpace
