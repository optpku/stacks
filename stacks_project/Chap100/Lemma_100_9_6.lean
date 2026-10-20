module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Immersion
import StacksCheckRecall

/-!
# Immersions induce embeddings of points of algebraic stacks

An immersion of algebraic stacks induces a topological embedding of underlying
point spaces onto a locally closed subset. Closed immersions induce closed
embeddings, and open immersions induce open embeddings.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 100.9.6: an immersion of algebraic stacks induces a topological
embedding onto a locally closed subset of the canonical point space. Closed
and open immersions induce closed and open embeddings, respectively. -/
@[stacks 0H20]
#check (AlgebraicGeometry.AlgebraicStack.isEmbedding_points :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    [Groupoids.Hom.Immersion f] →
      Topology.IsEmbedding (AlgebraicStack.Points.map f))

#check (AlgebraicGeometry.AlgebraicStack.isLocallyClosed_range_points :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    [Groupoids.Hom.Immersion f] →
      IsLocallyClosed (Set.range (AlgebraicStack.Points.map f)))

#check (AlgebraicGeometry.AlgebraicStack.isClosedEmbedding_points :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    [Groupoids.Hom.ClosedImmersion f] →
      Topology.IsClosedEmbedding (AlgebraicStack.Points.map f))

#check (AlgebraicGeometry.AlgebraicStack.isOpenEmbedding_points :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    [Groupoids.Hom.OpenImmersion f] →
      Topology.IsOpenEmbedding (AlgebraicStack.Points.map f))

#check (AlgebraicGeometry.AlgebraicStack.instClosed_of_closedImmersion :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    [Groupoids.Hom.ClosedImmersion f] → AlgebraicStack.Closed f)

#check (AlgebraicGeometry.AlgebraicStack.instOpen_of_openImmersion :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    [Groupoids.Hom.OpenImmersion f] → AlgebraicStack.Open f)
