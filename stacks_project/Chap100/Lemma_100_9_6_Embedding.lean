module

public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import stacks_project.Chap100.Definition_100_4_2_Points

/-!
# Embeddings of points of algebraic stacks

A morphism of algebraic stacks induces an embedding, closed embedding, or open
embedding on underlying point spaces when `Points.map f` has that property for
given topologies on `Points`. Competing topologies remain explicit parameters.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The map on points induced by `f` is a topological embedding with respect to the given
topologies on the source and target point spaces. -/
def isEmbeddingOnPoints {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y))
    (f : X ⟶ Y) : Prop :=
  @Topology.IsEmbedding (Points X) (Points Y) τX τY (Points.map f)

/-- Being an embedding on points means the induced map is inducing and injective. -/
theorem isEmbeddingOnPoints_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y))
    (f : X ⟶ Y) :
    isEmbeddingOnPoints τX τY f ↔
      @Topology.IsInducing (Points X) (Points Y) τX τY (Points.map f) ∧
        Function.Injective (Points.map f) :=
  sorry

/-- The image of `Points.map f` is a locally closed subset of the target point space. -/
def isLocallyClosedRangeOnPoints {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (τY : TopologicalSpace (Points Y)) (f : X ⟶ Y) : Prop :=
  @IsLocallyClosed (Points Y) τY (Set.range (Points.map f))

/-- A locally closed image of points is the intersection of an open set and a closed set. -/
theorem isLocallyClosedRangeOnPoints_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (τY : TopologicalSpace (Points Y)) (f : X ⟶ Y) :
    isLocallyClosedRangeOnPoints τY f ↔
      ∃ U C : Set (Points Y),
        @IsOpen (Points Y) τY U ∧ @IsClosed (Points Y) τY C ∧
          Set.range (Points.map f) = U ∩ C :=
  sorry

/-- The map on points induced by `f` is a closed embedding with respect to the given
topologies on the source and target point spaces. -/
def isClosedEmbeddingOnPoints {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y))
    (f : X ⟶ Y) : Prop :=
  @Topology.IsClosedEmbedding (Points X) (Points Y) τX τY (Points.map f)

/-- Being a closed embedding on points means the induced map is an embedding with closed
image. -/
theorem isClosedEmbeddingOnPoints_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y))
    (f : X ⟶ Y) :
    isClosedEmbeddingOnPoints τX τY f ↔
      isEmbeddingOnPoints τX τY f ∧
        @IsClosed (Points Y) τY (Set.range (Points.map f)) :=
  sorry

/-- The map on points induced by `f` is an open embedding with respect to the given
topologies on the source and target point spaces. -/
def isOpenEmbeddingOnPoints {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y))
    (f : X ⟶ Y) : Prop :=
  @Topology.IsOpenEmbedding (Points X) (Points Y) τX τY (Points.map f)

/-- Being an open embedding on points means the induced map is an embedding with open
image. -/
theorem isOpenEmbeddingOnPoints_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (τX : TopologicalSpace (Points X)) (τY : TopologicalSpace (Points Y))
    (f : X ⟶ Y) :
    isOpenEmbeddingOnPoints τX τY f ↔
      isEmbeddingOnPoints τX τY f ∧
        @IsOpen (Points Y) τY (Set.range (Points.map f)) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
