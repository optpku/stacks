/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

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

/-- A field-valued point of `X` over `S` is a morphism to `X` from the spectrum of
a field, as a 1-morphism of groupoid fibrations over `S` in the Hom-universe of
`CohStack.toGroupoids`. -/
structure FieldValuedPoint {S : Scheme.{u}}
    (X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)) where
  /-- The source field. -/
  K : Type u
  /-- The field structure on the source. -/
  [field : Field K]
  /-- The structure morphism of `Spec(K)` over `S`. -/
  structureHom : Spec (.of K) ⟶ S
  /-- The morphism `Spec(K) ⟶ X` of groupoid fibrations over `S`. -/
  hom : Classifying.slice (Over.mk structureHom) ⟶ X

namespace FieldValuedPoint

attribute [instance] field

variable {S : Scheme.{u}}
  {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}

/-- Construct a field-valued point from a field, a structure morphism to `S`, and
a morphism into `X`. -/
def of (K : Type u) [Field K] (structureHom : Spec (.of K) ⟶ S)
    (hom : Classifying.slice (Over.mk structureHom) ⟶ X) : FieldValuedPoint X where
  K := K
  structureHom := structureHom
  hom := hom

/-- The structure morphism of `FieldValuedPoint.of` is the given morphism to `S`. -/
@[simp]
theorem of_structureHom (K : Type u) [Field K] (structureHom : Spec (.of K) ⟶ S)
    (hom : Classifying.slice (Over.mk structureHom) ⟶ X) :
    (of K structureHom hom).structureHom = structureHom := sorry

/-- The morphism into `X` of `FieldValuedPoint.of` is the given morphism. -/
@[simp]
theorem of_hom (K : Type u) [Field K] (structureHom : Spec (.of K) ⟶ S)
    (hom : Classifying.slice (Over.mk structureHom) ⟶ X) :
    (of K structureHom hom).hom = hom := sorry

/-- The scheme over `S` given by the structure morphism of a field-valued point. -/
abbrev overObj (p : FieldValuedPoint X) : Over S :=
  Over.mk p.structureHom

/-- The structure morphism of `overObj p` is `p.structureHom`. -/
@[simp]
theorem overObj_hom (p : FieldValuedPoint X) : p.overObj.hom = p.structureHom :=
  sorry

/-- Postcompose a field-valued point with a 1-morphism of groupoid fibrations over
`S`. -/
def map {Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (p : FieldValuedPoint X) (f : X ⟶ Y) : FieldValuedPoint Y where
  K := p.K
  field := p.field
  structureHom := p.structureHom
  hom := p.hom ≫ f

/-- Postcomposition leaves the structure morphism unchanged. -/
@[simp]
theorem map_structureHom
    {Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (p : FieldValuedPoint X) (f : X ⟶ Y) :
    (p.map f).structureHom = p.structureHom := sorry

/-- The morphism of a postcomposed field-valued point is the evident composite. -/
@[simp]
theorem map_hom {Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (p : FieldValuedPoint X) (f : X ⟶ Y) :
    (p.map f).hom = p.hom ≫ f := sorry

/-- The field-valued point of `Classifying.toGroupoids F` associated to a
field-valued point of an algebraic space `F`. -/
def ofAlgebraicSpace {F : AlgebraicSpace S} (p : AlgebraicSpace.FieldValuedPoint F) :
    FieldValuedPoint (Classifying.toGroupoids F) :=
  of p.K p.structureHom
    ((Classifying.ofOverSliceEquiv p.overObj).inv ≫ Classifying.toGroupoids.map p.hom)

/-- `ofAlgebraicSpace` preserves the structure morphism to `S`. -/
theorem ofAlgebraicSpace_structureHom {F : AlgebraicSpace S}
    (p : AlgebraicSpace.FieldValuedPoint F) :
    (ofAlgebraicSpace p).structureHom = p.structureHom := sorry

/-- The morphism of `ofAlgebraicSpace p` is the slice comparison followed by
`Classifying.toGroupoids.map`. -/
theorem ofAlgebraicSpace_hom {F : AlgebraicSpace S}
    (p : AlgebraicSpace.FieldValuedPoint F) :
    (ofAlgebraicSpace p).hom =
      (Classifying.ofOverSliceEquiv p.overObj).inv ≫
        Classifying.toGroupoids.map p.hom := sorry

/-- A factorization from `p` to `q` is a morphism of source field spectra over
`S` making the triangle over `S` commute and filling the triangle over `X` by a
2-isomorphism. Existence of such a factorization says that `p` dominates `q`. -/
structure Factorization (p q : FieldValuedPoint X) where
  /-- The morphism of source field spectra. -/
  schemeHom : Spec (.of p.K) ⟶ Spec (.of q.K)
  /-- The triangle over `S` commutes. -/
  fac_structure : schemeHom ≫ q.structureHom = p.structureHom
  /-- The triangle over `X` 2-commutes. -/
  fac_iso :
    Classifying.overMap (Over.homMk schemeHom fac_structure) ≫ q.hom ≅ p.hom

namespace Factorization

/-- Construct a factorization from a morphism of field spectra, a commuting
triangle over `S`, and a 2-isomorphism over `X`. -/
def of {p q : FieldValuedPoint X} (schemeHom : Spec (.of p.K) ⟶ Spec (.of q.K))
    (fac_structure : schemeHom ≫ q.structureHom = p.structureHom)
    (fac_iso :
      Classifying.overMap (Over.homMk schemeHom fac_structure) ≫ q.hom ≅ p.hom) :
    Factorization p q where
  schemeHom := schemeHom
  fac_structure := fac_structure
  fac_iso := fac_iso

/-- A factorization is a morphism of field spectra making the `S`-triangle
commute and filling the `X`-triangle by a 2-isomorphism. -/
theorem spec {p q : FieldValuedPoint X} (φ : Factorization p q) :
    φ.schemeHom ≫ q.structureHom = p.structureHom ∧
      Nonempty
        (Classifying.overMap (Over.homMk φ.schemeHom φ.fac_structure) ≫ q.hom ≅
          p.hom) :=
  sorry

end Factorization

/-- A common extension of `p` and `q` is a field-valued point dominating both of
them. -/
structure CommonExtension (p q : FieldValuedPoint X) where
  /-- The common field-valued extension. -/
  point : FieldValuedPoint X
  /-- Its factorization through `p`. -/
  left : Factorization point p
  /-- Its factorization through `q`. -/
  right : Factorization point q

namespace CommonExtension

/-- Build a common extension from a field-valued point and factorizations through
`p` and `q`. -/
def of {p q : FieldValuedPoint X} (point : FieldValuedPoint X)
    (left : Factorization point p) (right : Factorization point q) :
    CommonExtension p q where
  point := point
  left := left
  right := right

/-- Reverse the two legs of a common extension. -/
def symm {p q : FieldValuedPoint X} (e : CommonExtension p q) :
    CommonExtension q p where
  point := e.point
  left := e.right
  right := e.left

end CommonExtension

/-- Field-valued points are equivalent when they admit a common field-valued
extension over `X`. -/
def Equivalent (p q : FieldValuedPoint X) : Prop :=
  Nonempty (CommonExtension p q)

/-- Equivalence of field-valued points is reflexive. -/
theorem Equivalent.refl (p : FieldValuedPoint X) : Equivalent p p := sorry

/-- Equivalence of field-valued points is symmetric. -/
theorem Equivalent.symm {p q : FieldValuedPoint X} :
    Equivalent p q → Equivalent q p := sorry

/-- Equivalence of field-valued points is transitive. -/
theorem Equivalent.trans {p q r : FieldValuedPoint X} :
    Equivalent p q → Equivalent q r → Equivalent p r := sorry

/-- Equivalence is preserved by postcomposition with a 1-morphism of groupoid
fibrations over `S`. -/
theorem Equivalent.map
    {Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    {p q : FieldValuedPoint X} (h : Equivalent p q) (f : X ⟶ Y) :
    Equivalent (p.map f) (q.map f) := sorry

/-- Equivalence of field-valued points of an algebraic space is preserved by
passage to `Classifying.toGroupoids`. -/
theorem Equivalent.ofAlgebraicSpace {F : AlgebraicSpace S}
    {p q : AlgebraicSpace.FieldValuedPoint F}
    (h : AlgebraicSpace.FieldValuedPoint.Equivalent p q) :
    Equivalent (ofAlgebraicSpace p) (ofAlgebraicSpace q) := sorry

/-- Equivalence of field-valued points is the existence of a field `Ω` and a
2-commutative square of morphisms of spectra over `S`. -/
theorem equivalent_iff (p q : FieldValuedPoint X) :
    Equivalent p q ↔
      ∃ (r : FieldValuedPoint X)
        (a : Spec (.of r.K) ⟶ Spec (.of p.K))
        (b : Spec (.of r.K) ⟶ Spec (.of q.K))
        (ha : a ≫ p.structureHom = r.structureHom)
        (hb : b ≫ q.structureHom = r.structureHom),
        Nonempty
          (Classifying.overMap (Over.homMk a ha : r.overObj ⟶ p.overObj) ≫ p.hom ≅
            Classifying.overMap (Over.homMk b hb : r.overObj ⟶ q.overObj) ≫ q.hom) :=
  sorry

end FieldValuedPoint

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
