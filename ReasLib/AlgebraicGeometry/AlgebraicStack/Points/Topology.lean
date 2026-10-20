/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Homeomorph.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Comparison
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Flat
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points
public import ReasLib.AlgebraicGeometry.GroupoidsOver.MorphismProperty
public import ReasLib.CategoryTheory.Fibered.Representable.Slice.Map

/-!
# Canonical topology on algebraic-stack points

The topology on points is tested by preimages along smooth surjective scheme
atlases. Such atlases present the point space as a quotient space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Topology
open FiberedCategoryOver.Groupoids (overMap)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace Points

/-- The map on points induced by a morphism `p : GroupoidsOver.slice U ⟶ X` from a
scheme over `S`. It sends a point `x` of `U` to the class of the residue-field
point of `x`, postcomposed with `p`. -/
def mapOfSlice {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {U : Over S} (p : GroupoidsOver.slice U ⟶ X) : U.left → Points X :=
  fun x ↦
    mk ((FieldValuedPoint.of (U.left.residueField x : Type u)
        (U.left.fromSpecResidueField x ≫ U.hom)
        (overMap (Over.homMk (U.left.fromSpecResidueField x)))).map p)

/-- `mapOfSlice p x` is the class of the residue-field point of `x`, postcomposed
with `p`. -/
theorem mapOfSlice_apply {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {U : Over S} (p : GroupoidsOver.slice U ⟶ X)
    (x : U.left) :
    mapOfSlice p x =
      mk ((FieldValuedPoint.of (U.left.residueField x : Type u)
          (U.left.fromSpecResidueField x ≫ U.hom)
          (overMap (Over.homMk (U.left.fromSpecResidueField x)))).map p) :=
  sorry

/-- The slice-to-points map is natural in morphisms of algebraic stacks. -/
theorem map_mapOfSlice {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {U : Over S}
    (p : GroupoidsOver.slice U ⟶ X) (f : X ⟶ Y) (x : U.left) :
    map f (mapOfSlice p x) = mapOfSlice (p ≫ f) x :=
  sorry

end Points

/-- A topology on the points of an algebraic stack is the canonical one when every
smooth surjective scheme atlas is a quotient map onto those points. -/
def IsPointsTopology {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    (τ : TopologicalSpace (Points X)) : Prop :=
  ∀ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
    Groupoids.Hom.Smooth p → Groupoids.Hom.Surjective p →
      @Topology.IsQuotientMap U.left (Points X)
        (inferInstance : TopologicalSpace U.left) τ (Points.mapOfSlice p)

/-- A topology is canonical on points of an algebraic stack exactly when every
smooth surjective scheme atlas is a quotient map. -/
theorem isPointsTopology_iff {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (τ : TopologicalSpace (Points X)) :
    IsPointsTopology X τ ↔
      ∀ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
        Groupoids.Hom.Smooth p → Groupoids.Hom.Surjective p →
          @Topology.IsQuotientMap U.left (Points X)
            (inferInstance : TopologicalSpace U.left) τ (Points.mapOfSlice p) :=
  sorry

/-- A canonical topology on points makes every smooth surjective scheme atlas a
quotient map. -/
theorem isPointsTopology_isQuotientMap {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {τ : TopologicalSpace (Points X)}
    (hτ : IsPointsTopology X τ) {U : Over S} {p : GroupoidsOver.slice U ⟶ X}
    (hp_smooth : Groupoids.Hom.Smooth p) (hp_surj : Groupoids.Hom.Surjective p) :
    @Topology.IsQuotientMap U.left (Points X)
      (inferInstance : TopologicalSpace U.left) τ (Points.mapOfSlice p) :=
  sorry

/-- Canonical topologies on the points of an algebraic stack are unique. -/
theorem isPointsTopology_unique {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {τ τ' : TopologicalSpace (Points X)}
    (hτ : IsPointsTopology X τ) (hτ' : IsPointsTopology X τ') : τ = τ' :=
  sorry

namespace Points

/-- The topology on stack points in which a subset is open precisely when its
preimage under every smooth surjective scheme atlas is open. -/
@[implicit_reducible]
def topology {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    TopologicalSpace (Points X) where
  IsOpen W := ∀ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
    Groupoids.Hom.Smooth p → Groupoids.Hom.Surjective p →
      IsOpen (mapOfSlice p ⁻¹' W)
  isOpen_univ := by
    intro U p hp_smooth hp_surj
    exact isOpen_univ
  isOpen_inter := by
    intro W V hW hV U p hp_smooth hp_surj
    exact (hW U p hp_smooth hp_surj).inter (hV U p hp_smooth hp_surj)
  isOpen_sUnion := by
    intro s hs U p hp_smooth hp_surj
    simpa only [Set.preimage_sUnion] using
      isOpen_biUnion (fun W hW ↦ hs W hW U p hp_smooth hp_surj)

end Points

/-- The atlas-tested topology on stack points makes every smooth surjective
scheme atlas a quotient map. -/
theorem isPointsTopology_pointsTopology {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] : IsPointsTopology X (Points.topology X) :=
  sorry

namespace Points

/-- A set of points of `X` is open when its preimage along every flat
locally-of-finite-presentation map from an algebraic space is open. -/
def isOpen {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (s : Set (Points X)) : Prop :=
  ∀ ⦃U : AlgebraicSpace S⦄ (p : U.toGroupoids ⟶ X)
    [Groupoids.Hom.Flat p] [Groupoids.Hom.LocallyOfFinitePresentation p],
    IsOpen (mapSpace p ⁻¹' s)

/-- The predicate `isOpen` is the final-openness condition along flat
locally-of-finite-presentation maps from algebraic spaces. -/
theorem isOpen_eq {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (s : Set (Points X)) :
    isOpen s ↔
      ∀ ⦃U : AlgebraicSpace S⦄ (p : U.toGroupoids ⟶ X)
        [Groupoids.Hom.Flat p] [Groupoids.Hom.LocallyOfFinitePresentation p],
        IsOpen (mapSpace p ⁻¹' s) :=
  Iff.rfl

end Points

/-- The canonical topology on the points of an algebraic stack over `S`. -/
instance instTopologicalSpacePoints {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] : TopologicalSpace (Points X) :=
  Points.topology X

namespace Points

/-- Open sets in the canonical topology are those whose preimages along every
flat locally-of-finite-presentation map from an algebraic space are open. -/
theorem isOpen_iff {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (s : Set (Points X)) :
    IsOpen s ↔
      ∀ ⦃U : AlgebraicSpace S⦄ (p : U.toGroupoids ⟶ X)
        [Groupoids.Hom.Flat p] [Groupoids.Hom.LocallyOfFinitePresentation p],
        IsOpen (mapSpace p ⁻¹' s) :=
  sorry

/-- Every 1-morphism of algebraic stacks over `S` induces a continuous map on
points. -/
theorem continuous_map {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Continuous (map f) :=
  sorry

/-- A flat locally-of-finite-presentation 1-morphism from an algebraic space is
continuous on points. -/
theorem continuous_mapSpace {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {U : AlgebraicSpace S} (p : U.toGroupoids ⟶ X)
    [Groupoids.Hom.Flat p] [Groupoids.Hom.LocallyOfFinitePresentation p] :
    Continuous (mapSpace p) :=
  sorry

/-- A flat locally-of-finite-presentation 1-morphism from an algebraic space is
open on points. -/
theorem isOpenMap_mapSpace {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {U : AlgebraicSpace S} (p : U.toGroupoids ⟶ X)
    [Groupoids.Hom.Flat p] [Groupoids.Hom.LocallyOfFinitePresentation p] :
    IsOpenMap (mapSpace p) :=
  sorry

/-- The canonical topology is coinduced by any smooth surjective scheme atlas. -/
theorem eq_coinduced_mapSlice {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {U : Over S} (p : GroupoidsOver.slice U ⟶ X)
    [Groupoids.Hom.Smooth p] [Groupoids.Hom.Surjective p] :
    instTopologicalSpacePoints X =
      TopologicalSpace.coinduced (mapSlice p) inferInstance :=
  sorry

/-- A smooth surjective scheme atlas is an open quotient map onto the points of
`X`. -/
theorem isOpenQuotientMap_mapSlice {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {U : Over S} (p : GroupoidsOver.slice U ⟶ X)
    [Groupoids.Hom.Smooth p] [Groupoids.Hom.Surjective p] :
    IsOpenQuotientMap (mapSlice p) :=
  sorry

/-- Passage from algebraic-space points to stack points is a homeomorphism onto
the canonical topology. -/
theorem ofAlgebraicSpace_isHomeomorph {S : Scheme.{u}} (F : AlgebraicSpace S) :
    IsHomeomorph (ofAlgebraicSpace : AlgebraicSpace.Points F → Points F.toGroupoids) :=
  sorry

end Points

/-- The canonical topology on points of algebraic stacks over `S`
makes every 1-morphism of algebraic stacks continuous on points, and makes every
flat locally-of-finite-presentation 1-morphism from an algebraic space continuous
and open on points. -/
theorem instTopologicalSpacePoints_spec (S : Scheme.{u}) :
    (∀ {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
      Continuous (Points.map f)) ∧
      ∀ {X : GroupoidsOver S} [AlgebraicStack X] {U : AlgebraicSpace S}
        (p : U.toGroupoids ⟶ X) [Groupoids.Hom.Flat p]
        [Groupoids.Hom.LocallyOfFinitePresentation p],
        Continuous (Points.mapSpace p) ∧ IsOpenMap (Points.mapSpace p) := by
  constructor
  · intro X Y hX hY f
    exact Points.continuous_map f
  · intro X hX U p hp_flat hp_lfp
    exact ⟨Points.continuous_mapSpace p, Points.isOpenMap_mapSpace p⟩

/-- A family of topologies on points of algebraic stacks over `S`
with functorial continuity and flat locally-of-finite-presentation openness from
algebraic spaces coincides with the canonical topology. -/
theorem Points.unique {S : Scheme.{u}}
    (τ : ∀ (X : GroupoidsOver S) [AlgebraicStack X], TopologicalSpace (Points X))
    (h_continuous : ∀ {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
      (f : X ⟶ Y), Continuous[τ X, τ Y] (Points.map f))
    (h_fppf : ∀ {X : GroupoidsOver S} [AlgebraicStack X] {U : AlgebraicSpace S}
      (p : U.toGroupoids ⟶ X) [Groupoids.Hom.Flat p]
      [Groupoids.Hom.LocallyOfFinitePresentation p],
      Continuous[inferInstance, τ X] (Points.mapSpace p) ∧
        @IsOpenMap (AlgebraicSpace.Points U) (Points X) inferInstance (τ X)
          (Points.mapSpace p))
    (X : GroupoidsOver S) [AlgebraicStack X] :
    τ X = instTopologicalSpacePoints X :=
  sorry

end AlgebraicGeometry.AlgebraicStack
