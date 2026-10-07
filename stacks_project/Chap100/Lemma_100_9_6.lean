module

public import stacks_project.Chap100.Definition_100_9_1_Immersion
public import stacks_project.Chap100.Lemma_100_9_6_Embedding
public import stacks_project.Chap101.Definition_101_13_2_Closed
public import stacks_project.Chap101.Lemma_101_11_3_UniversallyOpen

/-!
# Immersions induce embeddings of points of algebraic stacks

An immersion of algebraic stacks induces a topological embedding of underlying
point spaces onto a locally closed subset. Closed immersions induce closed
embeddings, and open immersions induce open embeddings.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 100.9.6 (1): If `f : X ⟶ Y` is an immersion of algebraic stacks, then
`Points.map f : |X| → |Y|` is a topological embedding, for the canonical
topologies on points. -/
@[stacks 0H20]
theorem isEmbedding_points {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Immersion f]
    (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y))
    (hX : IsPointsTopology X τX) (hY : IsPointsTopology Y τY) :
    isEmbeddingOnPoints τX τY f :=
  sorry

/-- Lemma 100.9.6 (2): If `f : X ⟶ Y` is an immersion of algebraic stacks, then
the image of `Points.map f` is a locally closed subset of `|Y|`, for the
canonical topology on points. -/
@[stacks 0H20]
theorem isLocallyClosed_range_points {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Immersion f]
    (τY : TopologicalSpace (Points Y)) (hY : IsPointsTopology Y τY) :
    isLocallyClosedRangeOnPoints τY f :=
  sorry

/-- Lemma 100.9.6 (3): If `f : X ⟶ Y` is a closed immersion of algebraic stacks,
then `Points.map f : |X| → |Y|` is a closed embedding, for the canonical
topologies on points. -/
@[stacks 0H20]
theorem isClosedEmbedding_points {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [ClosedImmersion f]
    (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y))
    (hX : IsPointsTopology X τX) (hY : IsPointsTopology Y τY) :
    isClosedEmbeddingOnPoints τX τY f :=
  sorry

/-- Lemma 100.9.6 (4): If `f : X ⟶ Y` is an open immersion of algebraic stacks,
then `Points.map f : |X| → |Y|` is an open embedding, for the canonical
topologies on points. -/
@[stacks 0H20]
theorem isOpenEmbedding_points {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [OpenImmersion f]
    (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y))
    (hX : IsPointsTopology X τX) (hY : IsPointsTopology Y τY) :
    isOpenEmbeddingOnPoints τX τY f :=
  sorry

/-- A closed immersion of algebraic stacks is a closed morphism. -/
instance instClosed_of_closedImmersion {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [ClosedImmersion f] :
    Closed f :=
  sorry

/-- An open immersion of algebraic stacks is an open morphism. -/
instance instOpen_of_openImmersion {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [OpenImmersion f] :
    Open f :=
  sorry

end AlgebraicGeometry.AlgebraicStack
