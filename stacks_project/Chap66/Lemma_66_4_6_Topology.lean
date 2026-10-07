module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Homeomorph.Defs
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_4_2_Comparison
public import stacks_project.Chap66.Lemma_66_5_5_PointsTopology

/-!
# Canonical topology on the points of an algebraic space

The space of points of an algebraic space over a scheme `S` carries a unique topology
making representable étale maps from schemes continuous and open, recovering the usual
scheme topology along `ofOver.pointsEquiv`, and making `|X| → |Y|` continuous for every
morphism of algebraic spaces over `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Points

-- Preserve the old named argument while reusing the canonical predicate.
attribute [deprecated_arg s subset (since := "2026-10-07")] isOpen

/-- The predicate `isOpen` is the final-openness condition along representable étale maps
from schemes. -/
theorem isOpen_eq {S : Scheme.{u}} {X : AlgebraicSpace S} (s : Set (Points X)) :
    isOpen s ↔
      ∀ ⦃U : Over S⦄ (p : ofOver U ⟶ X),
        (MorphismProperty.over (@Etale)).presheaf p → IsOpen (mapOfOver p ⁻¹' s) :=
  sorry

end Points

namespace Points

/-- Open sets in the canonical topology are those whose preimages along every representable
étale map from a scheme are open. -/
theorem isOpen_iff {S : Scheme.{u}} {X : AlgebraicSpace S} (s : Set (Points X)) :
    IsOpen s ↔
      ∀ ⦃U : Over S⦄ (p : ofOver U ⟶ X),
        (MorphismProperty.over (@Etale)).presheaf p → IsOpen (mapOfOver p ⁻¹' s) :=
  sorry

/-- Every morphism of algebraic spaces over `S` induces a continuous map on points. -/
theorem continuous_map {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Continuous (map f) :=
  sorry

/-- A representable étale morphism from a scheme is continuous on points. -/
theorem continuous_mapOfOver {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    (p : ofOver U ⟶ X) (hp : (MorphismProperty.over (@Etale)).presheaf p) :
    Continuous (mapOfOver p) :=
  sorry

/-- A representable étale morphism from a scheme is open on points. -/
theorem isOpenMap_mapOfOver {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    (p : ofOver U ⟶ X) (hp : (MorphismProperty.over (@Etale)).presheaf p) :
    IsOpenMap (mapOfOver p) :=
  sorry

/-- The canonical topology is coinduced by any representable étale locally-surjective atlas. -/
theorem eq_coinduced_mapOfOver {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    (p : ofOver U ⟶ X) (hp : (MorphismProperty.over (@Etale)).presheaf p)
    (hsurj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p) :
    instTopologicalSpacePoints X = TopologicalSpace.coinduced (mapOfOver p) inferInstance :=
  sorry

/-- A representable étale locally-surjective atlas is an open quotient map onto the points of
`X`. -/
theorem isOpenQuotientMap_mapOfOver {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    (p : ofOver U ⟶ X) (hp : (MorphismProperty.over (@Etale)).presheaf p)
    (hsurj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p) :
    IsOpenQuotientMap (mapOfOver p) :=
  sorry

end Points

namespace ofOver

/-- The identification of Lemma 66.4.2 is a homeomorphism onto the canonical topology on
points of a representable algebraic space. -/
def pointsHomeomorph {S : Scheme.{u}} (X : Over S) : X.left ≃ₜ Points (ofOver X) :=
  Homeomorph.mk (pointsEquiv X) sorry sorry

/-- The underlying equivalence of `pointsHomeomorph` is `pointsEquiv`. -/
theorem pointsHomeomorph_toEquiv {S : Scheme.{u}} (X : Over S) :
    (pointsHomeomorph X).toEquiv = pointsEquiv X :=
  sorry

/-- The identification of scheme points with algebraic-space points is a homeomorphism. -/
theorem pointsEquiv_isHomeomorph {S : Scheme.{u}} (X : Over S) :
    IsHomeomorph (pointsEquiv X) :=
  sorry

/-- On a representable algebraic space the canonical topology is coinduced along
`pointsEquiv`. -/
theorem pointsEquiv_eq_coinduced {S : Scheme.{u}} (X : Over S) :
    instTopologicalSpacePoints (ofOver X) =
      TopologicalSpace.coinduced (pointsEquiv X) inferInstance :=
  sorry

end ofOver

end AlgebraicGeometry.AlgebraicSpace
