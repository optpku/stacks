/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Definition_66_4_1_Points
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

/-- The map on points induced by `f` is a topological embedding with respect to the given
topologies on the source and target point spaces. -/
def isEmbeddingOnPoints {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (τZ : TopologicalSpace (Points Z)) (τX : TopologicalSpace (Points X))
    (f : Z ⟶ X) : Prop :=
  @Topology.IsEmbedding (Points Z) (Points X) τZ τX (Points.map f)

/-- Being an embedding on points means the induced map is inducing and injective. -/
theorem isEmbeddingOnPoints_iff {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (τZ : TopologicalSpace (Points Z)) (τX : TopologicalSpace (Points X))
    (f : Z ⟶ X) :
    isEmbeddingOnPoints τZ τX f ↔
      @Topology.IsInducing (Points Z) (Points X) τZ τX (Points.map f) ∧
        Function.Injective (Points.map f) :=
  sorry

/-- The image of `Points.map f` is a locally closed subset of the target point space. -/
def isLocallyClosedRangeOnPoints {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (τX : TopologicalSpace (Points X)) (f : Z ⟶ X) : Prop :=
  @IsLocallyClosed (Points X) τX (Set.range (Points.map f))

/-- A locally closed image of points is the intersection of an open set and a closed set. -/
theorem isLocallyClosedRangeOnPoints_iff {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (τX : TopologicalSpace (Points X)) (f : Z ⟶ X) :
    isLocallyClosedRangeOnPoints τX f ↔
      ∃ U C : Set (Points X),
        @IsOpen (Points X) τX U ∧ @IsClosed (Points X) τX C ∧
          Set.range (Points.map f) = U ∩ C :=
  sorry

namespace IsImmersion

/-- Lemma 66.12.1 (1): let `S` be a scheme. Let `f : Z ⟶ X` be an immersion of algebraic
spaces over `S`. Then `Points.map f : Points Z → Points X` is a topological embedding, for
the canonical topologies on points presented by open-quotient étale atlases. -/
@[stacks 0ABJ]
theorem isEmbedding_points {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (f : Z ⟶ X) [IsImmersion f]
    (τZ : TopologicalSpace (Points Z)) (AZ : Points.OpenQuotientAtlas Z τZ)
    (τX : TopologicalSpace (Points X)) (AX : Points.OpenQuotientAtlas X τX) :
    isEmbeddingOnPoints τZ τX f :=
  sorry

/-- Lemma 66.12.1 (2): let `S` be a scheme. Let `f : Z ⟶ X` be an immersion of algebraic
spaces over `S`. Then the image of `Points.map f` is a locally closed subset of `Points X`,
for the canonical topology presented by an open-quotient étale atlas. -/
@[stacks 0ABJ]
theorem isLocallyClosed_range_points {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (f : Z ⟶ X) [IsImmersion f]
    (τX : TopologicalSpace (Points X)) (AX : Points.OpenQuotientAtlas X τX) :
    isLocallyClosedRangeOnPoints τX f :=
  sorry

end IsImmersion

end AlgebraicGeometry.AlgebraicSpace
