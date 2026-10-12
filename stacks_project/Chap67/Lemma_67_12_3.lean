/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_12_1
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Topology

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.12.3 (1): let `S` be a scheme. Let `i : Z ⟶ X` be an immersion of
algebraic spaces over `S`. Then `Points.map i : Points Z → Points X` is a
homeomorphism onto a locally closed subset, for the canonical topologies on
points presented by open-quotient étale atlases. -/
@[stacks 04CD] #check IsImmersion.isEmbedding_points
@[stacks 04CD] #check IsImmersion.isLocallyClosed_range_points

namespace IsImmersion

/-- Lemma 67.12.3 (2): let `S` be a scheme. Let `f : Z ⟶ X` be an immersion of
algebraic spaces over `S`. Then `f` is a closed immersion if and only if the
image of `Points.map f` is a closed subset of `Points X`, for the canonical
topology presented by an open-quotient étale atlas. -/
@[stacks 04CD]
theorem isClosedImmersion_iff_isClosed_range_points {S : Scheme.{u}}
    {Z X : AlgebraicSpace S} (f : Z ⟶ X) [IsImmersion f]
    (τX : TopologicalSpace (Points X)) (AX : Points.OpenQuotientAtlas X τX) :
    IsClosedImmersion f ↔ @IsClosed (Points X) τX (Set.range (Points.map f)) :=
  sorry

/-- An immersion of algebraic spaces whose image of points is closed, for the
canonical topology presented by an open-quotient étale atlas, is a closed
immersion. -/
theorem of_isClosed_range_points {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (f : Z ⟶ X) [IsImmersion f] (τX : TopologicalSpace (Points X))
    (AX : Points.OpenQuotientAtlas X τX)
    (h : @IsClosed (Points X) τX (Set.range (Points.map f))) :
    IsClosedImmersion f :=
  sorry

end IsImmersion

namespace IsClosedImmersion

/-- A closed immersion of algebraic spaces has closed image of points, for the
canonical topology presented by an open-quotient étale atlas. -/
theorem isClosed_range_points {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (f : Z ⟶ X) [IsClosedImmersion f] (τX : TopologicalSpace (Points X))
    (AX : Points.OpenQuotientAtlas X τX) :
    @IsClosed (Points X) τX (Set.range (Points.map f)) :=
  sorry

end IsClosedImmersion

end AlgebraicGeometry.AlgebraicSpace
