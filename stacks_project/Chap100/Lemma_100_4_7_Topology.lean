/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Homeomorph.Defs
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap94.Definition_94_12_1_MorphismProperty
public import stacks_project.Chap96.Lemma_96_19_10_LocallyOfFinitePresentation
public import stacks_project.Chap100.Lemma_100_3_3
public import stacks_project.Chap100.Definition_100_4_2_Points
public import stacks_project.Chap100.Lemma_100_7_4_Points

/-!
# Canonical topology on the points of an algebraic stack

The space of points of an algebraic stack over a scheme `S` carries a unique
topology making every 1-morphism of algebraic stacks continuous on points, and
making every flat locally-of-finite-presentation 1-morphism from an algebraic
space continuous and open on points, with `|U|` carrying the canonical
algebraic-space topology.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

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
  sorry

end Points

/-- The canonical topology on the points of an algebraic stack over `S`. -/
instance instTopologicalSpacePoints {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] : TopologicalSpace (Points X) where
  IsOpen := Points.isOpen
  isOpen_univ := sorry
  isOpen_inter := sorry
  isOpen_sUnion := sorry

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

end AlgebraicGeometry.AlgebraicStack
