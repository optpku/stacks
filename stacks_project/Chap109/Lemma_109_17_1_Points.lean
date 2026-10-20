/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.FieldValuedPoint

public import Mathlib.Topology.Defs.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap108.Lemma_108_4_2_LocallyOfFinitePresentation
public import stacks_project.Chap108.Lemma_108_4_3_Existence
public import stacks_project.Chap108.Lemma_108_4_8_Algebraic
public import stacks_project.Chap108.Lemma_108_4_8_Flat

/-!
# Points of a CohStack-sized algebraic stack

A point of a category fibred in groupoids `X` over a scheme `S`, in the
Hom-universe of `CohStack.toGroupoids`, is an equivalence class of morphisms
`Classifying.slice (Spec K) ⟶ X` from spectra of fields. Two such morphisms
are equivalent when they become 2-isomorphic after restriction along a common
field extension. The canonical topology tests openness by pullback along flat
locally-of-finite-presentation maps from algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupScheme
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack



/-- The setoid of field-valued points of an algebraic stack, with relation the
common-extension equivalence. -/
def equivalentSetoid {S : Scheme.{u}}
    (X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S))
    [AlgebraicStack X] : Setoid (FieldValuedPoint X) where
  r := FieldValuedPoint.Equivalent
  iseqv := sorry

/-- The setoid relation is the common-extension equivalence of field-valued
points. -/
@[simp]
theorem equivalentSetoid_rel_iff {S : Scheme.{u}}
    {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack X] (p q : FieldValuedPoint X) :
    equivalentSetoid X p q ↔ FieldValuedPoint.Equivalent p q := sorry

/-- The set of points of an algebraic stack, as equivalence classes of morphisms
from spectra of fields. -/
def Points {S : Scheme.{u}}
    (X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S))
    [AlgebraicStack X] : Type (u + 1) :=
  Quotient (equivalentSetoid X)

namespace Points

variable {S : Scheme.{u}}
  {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
  [AlgebraicStack X]

/-- The class of a field-valued point. -/
def mk (p : FieldValuedPoint X) : Points X :=
  Quotient.mk (equivalentSetoid X) p

/-- Two field-valued points determine the same point of `X` exactly when they
admit a common field-valued extension. -/
@[simp]
theorem mk_eq_mk_iff (p q : FieldValuedPoint X) :
    mk p = mk q ↔ FieldValuedPoint.Equivalent p q := sorry

/-- The map on points induced by a morphism of algebraic stacks over `S`. -/
def map {Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack Y] (f : X ⟶ Y) : Points X → Points Y :=
  Quotient.map (fun p ↦ p.map f) fun _ _ h ↦ FieldValuedPoint.Equivalent.map h f

/-- The induced map on points sends the class of a representative to the class of
its postcomposition. -/
@[simp]
theorem map_mk {Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack Y] (f : X ⟶ Y) (p : FieldValuedPoint X) :
    map f (mk p) = mk (p.map f) := sorry

/-- The identity morphism of algebraic stacks induces the identity on points. -/
@[simp]
theorem map_id (x : Points X) : map (𝟙 X) x = x := sorry

/-- The induced map on points preserves composition. -/
@[simp]
theorem map_comp {Y Z : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack Y] [AlgebraicStack Z] (f : X ⟶ Y) (g : Y ⟶ Z) (x : Points X) :
    map (f ≫ g) x = map g (map f x) := sorry

/-- The image in `|Classifying.toGroupoids F|` of a point of an algebraic space
`F`. -/
def ofAlgebraicSpace {F : AlgebraicSpace S} (x : AlgebraicSpace.Points F) :
    Points (Classifying.toGroupoids F) :=
  Quotient.map (fun p : AlgebraicSpace.FieldValuedPoint F ↦
      FieldValuedPoint.ofAlgebraicSpace p)
    (fun _ _ h ↦ FieldValuedPoint.Equivalent.ofAlgebraicSpace h) x

/-- Passage to stack points sends the class of a field-valued point to the class
of its associated field-valued point of `Classifying.toGroupoids F`. -/
theorem ofAlgebraicSpace_mk {F : AlgebraicSpace S}
    (p : AlgebraicSpace.FieldValuedPoint F) :
    ofAlgebraicSpace (AlgebraicSpace.Points.mk p) =
      mk (FieldValuedPoint.ofAlgebraicSpace p) := sorry

/-- The image in `|X|` of a point of an algebraic space `F` along a morphism
`Classifying.toGroupoids F ⟶ X`. -/
def mapSpace {F : AlgebraicSpace S} (p : Classifying.toGroupoids F ⟶ X)
    (u : AlgebraicSpace.Points F) : Points X :=
  map p (ofAlgebraicSpace u)

/-- `mapSpace p u` is the image of `ofAlgebraicSpace u` under `Points.map p`. -/
theorem mapSpace_apply {F : AlgebraicSpace S} (p : Classifying.toGroupoids F ⟶ X)
    (u : AlgebraicSpace.Points F) :
    mapSpace p u = map p (ofAlgebraicSpace u) := sorry

/-- A set of points of `X` is open when its preimage along every flat
locally-of-finite-presentation map from an algebraic space is open. -/
def isOpen (s : Set (Points X)) : Prop :=
  ∀ ⦃U : AlgebraicSpace S⦄ (p : Classifying.toGroupoids U ⟶ X)
    [Hom.Flat p] [Hom.LocallyOfFinitePresentation p],
    IsOpen (mapSpace p ⁻¹' s)

/-- The predicate `isOpen` is the final-openness condition along flat
locally-of-finite-presentation maps from algebraic spaces. -/
theorem isOpen_eq (s : Set (Points X)) :
    isOpen s ↔
      ∀ ⦃U : AlgebraicSpace S⦄ (p : Classifying.toGroupoids U ⟶ X)
        [Hom.Flat p] [Hom.LocallyOfFinitePresentation p],
        IsOpen (mapSpace p ⁻¹' s) :=
  sorry

end Points

/-- The canonical topology on the points of an algebraic stack over `S` in the
Hom-universe of `CohStack.toGroupoids`. -/
instance instTopologicalSpacePoints {S : Scheme.{u}}
    (X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S))
    [AlgebraicStack X] : TopologicalSpace (Points X) where
  IsOpen := Points.isOpen
  isOpen_univ := sorry
  isOpen_inter := sorry
  isOpen_sUnion := sorry

namespace Points

variable {S : Scheme.{u}}
  {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
  [AlgebraicStack X]

/-- Open sets in the canonical topology are those whose preimages along every
flat locally-of-finite-presentation map from an algebraic space are open. -/
theorem isOpen_iff (s : Set (Points X)) :
    IsOpen s ↔
      ∀ ⦃U : AlgebraicSpace S⦄ (p : Classifying.toGroupoids U ⟶ X)
        [Hom.Flat p] [Hom.LocallyOfFinitePresentation p],
        IsOpen (mapSpace p ⁻¹' s) :=
  sorry

/-- Every 1-morphism of algebraic stacks over `S` induces a continuous map on
points. -/
theorem continuous_map
    {Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack Y] (f : X ⟶ Y) : Continuous (map f) :=
  sorry

end Points

end AlgebraicGeometry.AlgebraicSpace.CohStack
