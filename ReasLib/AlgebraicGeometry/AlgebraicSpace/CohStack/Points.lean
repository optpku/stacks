/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Algebraic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.FieldValuedPoint

/-!
# Points of lifted algebraic stacks

Points are common-extension equivalence classes of field-valued representatives.
Morphisms act by postcomposition on representatives.
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
  iseqv :=
    { refl := FieldValuedPoint.Equivalent.refl
      symm := FieldValuedPoint.Equivalent.symm
      trans := FieldValuedPoint.Equivalent.trans }

/-- The setoid relation is the common-extension equivalence of field-valued
points. -/
@[simp]
theorem equivalentSetoid_rel_iff {S : Scheme.{u}}
    {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    [AlgebraicStack X] (p q : FieldValuedPoint X) :
    equivalentSetoid X p q ↔ FieldValuedPoint.Equivalent p q := Iff.rfl

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
    map f (mk p) = mk (p.map f) := rfl

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
      mk (FieldValuedPoint.ofAlgebraicSpace p) := rfl

/-- The image in `|X|` of a point of an algebraic space `F` along a morphism
`Classifying.toGroupoids F ⟶ X`. -/
def mapSpace {F : AlgebraicSpace S} (p : Classifying.toGroupoids F ⟶ X)
    (u : AlgebraicSpace.Points F) : Points X :=
  map p (ofAlgebraicSpace u)

/-- `mapSpace p u` is the image of `ofAlgebraicSpace u` under `Points.map p`. -/
theorem mapSpace_apply {F : AlgebraicSpace S} (p : Classifying.toGroupoids F ⟶ X)
    (u : AlgebraicSpace.Points F) :
    mapSpace p u = map p (ofAlgebraicSpace u) := rfl

end Points

end AlgebraicGeometry.AlgebraicSpace.CohStack
