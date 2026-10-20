/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.Topology.Defs.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Comparison

/-!
# Canonical topology on algebraic-space points

Openness is tested by pullback along representable étale morphisms from schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Topology

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Points

/-- A morphism from a scheme over `S` induces a map from scheme points to
algebraic-space points. -/
def mapOfOver {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S} (p : ofOver U ⟶ X) :
    U.left → Points X :=
  fun point ↦ map p (ofOver.pointsEquiv U point)

/-- The map on scheme points is the composite of `ofOver.pointsEquiv` with `Points.map`. -/
@[simp]
theorem mapOfOver_apply {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    (p : ofOver U ⟶ X) (point : U.left) :
    mapOfOver p point = map p (ofOver.pointsEquiv U point) := sorry

/-- A subset of algebraic-space points is open when its preimage along every
representable étale morphism from a scheme is open. -/
def isOpen {S : Scheme.{u}} {X : AlgebraicSpace S} (subset : Set (Points X)) : Prop :=
  ∀ ⦃U : Over S⦄ (p : ofOver U ⟶ X),
    (MorphismProperty.over (@Etale)).presheaf p → IsOpen (mapOfOver p ⁻¹' subset)

/-- The whole point space satisfies the atlas-tested openness predicate. -/
theorem isOpen_univ {S : Scheme.{u}} {X : AlgebraicSpace S} :
    isOpen (Set.univ : Set (Points X)) := sorry

/-- Intersections preserve atlas-tested openness. -/
theorem isOpen_inter {S : Scheme.{u}} {X : AlgebraicSpace S}
    (s t : Set (Points X)) (hs : isOpen s) (ht : isOpen t) :
    isOpen (s ∩ t) := sorry

/-- Arbitrary unions preserve atlas-tested openness. -/
theorem isOpen_sUnion {S : Scheme.{u}} {X : AlgebraicSpace S}
    (s : Set (Set (Points X))) (hs : ∀ t ∈ s, isOpen t) :
    isOpen (⋃₀ s) := sorry

end Points

/-- The canonical topology on algebraic-space points tests openness along
representable étale morphisms from schemes. -/
instance instTopologicalSpacePoints {S : Scheme.{u}} (X : AlgebraicSpace S) :
    TopologicalSpace (Points X) where
  IsOpen := Points.isOpen
  isOpen_univ := Points.isOpen_univ
  isOpen_inter := Points.isOpen_inter
  isOpen_sUnion := Points.isOpen_sUnion


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

/-- Scheme points map continuously to points of the associated algebraic space. -/
theorem continuous_pointsEquiv {S : Scheme.{u}} (X : Over S) :
    Continuous (pointsEquiv X) := sorry

/-- Points of a representable algebraic space map continuously to its scheme points. -/
theorem continuous_pointsEquiv_symm {S : Scheme.{u}} (X : Over S) :
    Continuous (pointsEquiv X).symm := sorry

/-- Scheme points are homeomorphic to points of the associated algebraic space. -/
def pointsHomeomorph {S : Scheme.{u}} (X : Over S) : X.left ≃ₜ Points (ofOver X) :=
  Homeomorph.mk (pointsEquiv X) (continuous_pointsEquiv X) (continuous_pointsEquiv_symm X)

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

namespace Points

/-- A family of topologies recovering scheme topology, making every morphism continuous,
and making every representable étale map from a scheme continuous and open agrees with the
canonical topology. -/
@[stacks 03BX]
theorem unique {S : Scheme.{u}}
    (τ : ∀ X : AlgebraicSpace S, TopologicalSpace (Points X))
    (h_scheme : ∀ X : Over S,
      τ (ofOver X) = TopologicalSpace.coinduced (ofOver.pointsEquiv X) inferInstance)
    (h_continuous : ∀ {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      Continuous[τ X, τ Y] (Points.map f))
    (h_etale : ∀ {X : AlgebraicSpace S} {U : Over S} (p : ofOver U ⟶ X),
      (MorphismProperty.over (@Etale)).presheaf p →
        Continuous[inferInstance, τ X] (Points.mapOfOver p) ∧
          @IsOpenMap U.left (Points X) inferInstance (τ X) (Points.mapOfOver p))
    (X : AlgebraicSpace S) :
    τ X = instTopologicalSpacePoints X :=
  sorry

/-- There is a unique family of topologies on algebraic-space points recovering scheme
topology, making every morphism continuous, and making every representable étale map from a
scheme continuous and open. -/
theorem existsUnique_topology (S : Scheme.{u}) :
    ∃! τ : ∀ X : AlgebraicSpace S, TopologicalSpace (Points X),
      (∀ U : Over S,
        τ (ofOver U) = TopologicalSpace.coinduced (ofOver.pointsEquiv U) inferInstance) ∧
      (∀ {X Y : AlgebraicSpace S} (f : X ⟶ Y),
        Continuous[τ X, τ Y] (Points.map f)) ∧
      (∀ {X : AlgebraicSpace S} {U : Over S} (p : ofOver U ⟶ X),
        (MorphismProperty.over (@Etale)).presheaf p →
          Continuous[inferInstance, τ X] (Points.mapOfOver p) ∧
            @IsOpenMap U.left (Points X) inferInstance (τ X) (Points.mapOfOver p)) := by
  refine ⟨fun X ↦ instTopologicalSpacePoints X, ?_, ?_⟩
  · refine ⟨fun U ↦ ofOver.pointsEquiv_eq_coinduced U, ?_, ?_⟩
    · intro X Y f
      exact continuous_map f
    · intro X U p hp
      exact ⟨continuous_mapOfOver p hp, isOpenMap_mapOfOver p hp⟩
  · intro τ hτ
    funext X
    exact unique τ hτ.1 hτ.2.1 hτ.2.2 X

end Points

end AlgebraicGeometry.AlgebraicSpace
