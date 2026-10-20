module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Immersion
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Topology

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.12.3: an immersion of algebraic spaces over a scheme is a closed
immersion if and only if its image on canonical point spaces is closed. -/
@[stacks 04CD] #check
  (AlgebraicGeometry.AlgebraicSpace.IsImmersion.isClosedImmersion_iff_isClosed_range_points :
    ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (f : Z ⟶ X) [IsImmersion f],
      IsClosedImmersion f ↔ IsClosed (Set.range (Points.map f)))

#check (AlgebraicGeometry.AlgebraicSpace.IsImmersion.isEmbedding_points :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (f : Z ⟶ X) [IsImmersion f],
    Topology.IsEmbedding (Points.map f))

#check (AlgebraicGeometry.AlgebraicSpace.IsImmersion.isLocallyClosed_range_points :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (f : Z ⟶ X) [IsImmersion f],
    IsLocallyClosed (Set.range (Points.map f)))

#check (AlgebraicGeometry.AlgebraicSpace.IsImmersion.of_isClosed_range_points :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (f : Z ⟶ X) [IsImmersion f],
    IsClosed (Set.range (Points.map f)) → IsClosedImmersion f)

#check (AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion.isClosed_range_points :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (f : Z ⟶ X) [IsClosedImmersion f],
    IsClosed (Set.range (Points.map f)))

end AlgebraicGeometry.AlgebraicSpace
