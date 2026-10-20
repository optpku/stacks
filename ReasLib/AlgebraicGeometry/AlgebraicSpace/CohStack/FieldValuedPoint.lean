module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points

/-!
# Field-valued points of lifted groupoid fibrations
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

end AlgebraicGeometry.AlgebraicSpace.CohStack
