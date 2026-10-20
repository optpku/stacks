module

public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.InducedCategory
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism

/-!
# Points of an algebraic space

A point of an algebraic space `X` over a scheme `S` is an equivalence class of morphisms
`Spec(K) ⟶ X` from spectra of fields, as objects of `Sch/S`. Two such morphisms are equivalent
when they become equal after restriction along a common field extension.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The morphism of algebraic spaces over `S` induced by a morphism of schemes over `S`. -/
def ofOverMap {S : Scheme.{u}} {U V : Over S} (f : U ⟶ V) : ofOver U ⟶ ofOver V :=
  (yoneda.map f : yoneda.obj U ⟶ yoneda.obj V)

/-- `ofOverMap f` is the Yoneda image of a morphism of schemes over `S`. -/
theorem ofOverMap_eq {S : Scheme.{u}} {U V : Over S} (f : U ⟶ V) :
    ofOverMap f = yoneda.map f := sorry

/-- The morphism of algebraic spaces over `S` induced by a morphism of schemes compatible with the
given structure morphisms. -/
def ofOverHomMk {S : Scheme.{u}} {XK XL : Scheme.{u}} {σK : XK ⟶ S} {σL : XL ⟶ S}
    (f : XK ⟶ XL) (hf : f ≫ σL = σK) : ofOver (Over.mk σK) ⟶ ofOver (Over.mk σL) :=
  ofOverMap (Over.homMk f hf)

/-- `ofOverHomMk f hf` is `ofOverMap` of the corresponding morphism in `Over S`. -/
theorem ofOverHomMk_eq {S : Scheme.{u}} {XK XL : Scheme.{u}} {σK : XK ⟶ S} {σL : XL ⟶ S}
    (f : XK ⟶ XL) (hf : f ≫ σL = σK) :
    ofOverHomMk f hf = ofOverMap (Over.homMk f hf) := sorry

set_option backward.privateInPublic true in
/-- Explicit field and morphism data for a field-valued point of an algebraic space. -/
private structure FieldValuedPointObj {S : Scheme.{u}} (X : AlgebraicSpace S) where
  /-- The source field. -/
  K : Type u
  /-- The field structure on the source. -/
  [field : Field K]
  /-- The structure morphism of `Spec(K)` over `S`. -/
  structureHom : Spec (.of K) ⟶ S
  /-- The morphism `Spec(K) ⟶ X` of algebraic spaces over `S`. -/
  hom : ofOver (Over.mk structureHom) ⟶ X

set_option backward.privateInPublic true in
/-- The slice object over `X` determined by the stored field-valued morphism. -/
private def FieldValuedPointObj.over {S : Scheme.{u}} {X : AlgebraicSpace S}
    (p : FieldValuedPointObj X) : Over X :=
  Over.mk p.hom

set_option backward.privateInPublic true in
/-- Field-valued points with morphisms induced from the slice category over the algebraic space. -/
abbrev FieldValuedPoint {S : Scheme.{u}} (X : AlgebraicSpace S) :=
  InducedCategory (Over X) (FieldValuedPointObj.over (X := X))

namespace FieldValuedPoint

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

set_option backward.privateInPublic true in
/-- The source-field carrier of a field-valued point. -/
abbrev K (p : FieldValuedPoint X) : Type u := FieldValuedPointObj.K p

set_option backward.privateInPublic true in
/-- The field structure stored in a field-valued point. -/
abbrev field (p : FieldValuedPoint X) : Field p.K := FieldValuedPointObj.field p

attribute [instance] field

set_option backward.privateInPublic true in
/-- The structure morphism from the source-field spectrum to the base scheme. -/
abbrev structureHom (p : FieldValuedPoint X) : Spec (.of p.K) ⟶ S :=
  FieldValuedPointObj.structureHom p

set_option backward.privateInPublic true in
/-- The morphism from the source-field spectrum into the algebraic space. -/
abbrev hom (p : FieldValuedPoint X) : ofOver (Over.mk p.structureHom) ⟶ X :=
  FieldValuedPointObj.hom p

set_option backward.privateInPublic true in
/-- The object over `X` determined by the field-valued point. -/
def over (p : FieldValuedPoint X) : Over X := FieldValuedPointObj.over p

/-- The induced embedding of field-valued points into the slice over `X`. -/
def toOver (X : AlgebraicSpace S) : FieldValuedPoint X ⥤ Over X :=
  inducedFunctor FieldValuedPoint.over

/-- The induced slice embedding of field-valued points is fully faithful. -/
def toOverFullyFaithful (X : AlgebraicSpace S) : (toOver X).FullyFaithful :=
  fullyFaithfulInducedFunctor FieldValuedPoint.over

set_option backward.privateInPublic true in
/-- Construct a field-valued point from a field, a structure morphism to `S`, and a morphism into
`X`. -/
def of (K : Type u) [Field K] (structureHom : Spec (.of K) ⟶ S)
    (hom : ofOver (Over.mk structureHom) ⟶ X) : FieldValuedPoint X :=
  ⟨K, structureHom, hom⟩

/-- The structure morphism of `FieldValuedPoint.of` is the given morphism to `S`. -/
@[simp]
theorem of_structureHom (K : Type u) [Field K] (structureHom : Spec (.of K) ⟶ S)
    (hom : ofOver (Over.mk structureHom) ⟶ X) :
    (of K structureHom hom).structureHom = structureHom := sorry

/-- The morphism into `X` of `FieldValuedPoint.of` is the given morphism. -/
@[simp]
theorem of_hom (K : Type u) [Field K] (structureHom : Spec (.of K) ⟶ S)
    (hom : ofOver (Over.mk structureHom) ⟶ X) :
    (of K structureHom hom).hom = hom := sorry

/-- The scheme over `S` given by the structure morphism of a field-valued point. -/
abbrev overObj (p : FieldValuedPoint X) : Over S :=
  Over.mk p.structureHom

/-- The structure morphism of `overObj p` is `p.structureHom`. -/
@[simp]
theorem overObj_hom (p : FieldValuedPoint X) : p.overObj.hom = p.structureHom := sorry

set_option backward.privateInPublic true in
/-- Postcompose a field-valued point with a morphism of algebraic spaces over `S`. -/
def map {Y : AlgebraicSpace S} (p : FieldValuedPoint X) (f : X ⟶ Y) : FieldValuedPoint Y :=
  { K := p.K
    field := p.field
    structureHom := p.structureHom
    hom := p.hom ≫ f }

/-- Postcomposition leaves the structure morphism unchanged. -/
@[simp]
theorem map_structureHom {Y : AlgebraicSpace S} (p : FieldValuedPoint X) (f : X ⟶ Y) :
    (p.map f).structureHom = p.structureHom := sorry

/-- The morphism of a postcomposed field-valued point is the evident composite. -/
@[simp]
theorem map_hom {Y : AlgebraicSpace S} (p : FieldValuedPoint X) (f : X ⟶ Y) :
    (p.map f).hom = p.hom ≫ f := sorry

/-- The Yoneda element `p ∈ X(Spec(K))` determined by a field-valued point. -/
def elem (p : FieldValuedPoint X) : X.functorOfPoints.obj (op p.overObj) :=
  yonedaEquiv (p.hom : yoneda.obj p.overObj ⟶ X.functorOfPoints)

/-- The Yoneda element of a field-valued point recovers its morphism into `X`. -/
theorem elem_spec (p : FieldValuedPoint X) :
    yonedaEquiv.symm p.elem = p.hom := sorry

/-- A factorization from `p` to `q` is a morphism of source field spectra over `S` compatible with
the morphisms into `X`. Existence of such a factorization says that `p` dominates `q`. -/
structure Factorization (p q : FieldValuedPoint X) where
  /-- The morphism of source field spectra. -/
  schemeHom : p.overObj.left ⟶ q.overObj.left
  /-- The triangle over `S` commutes. -/
  fac_structure : schemeHom ≫ q.structureHom = p.structureHom
  /-- The triangle over `X` commutes. -/
  fac_hom : ofOverHomMk schemeHom fac_structure ≫ q.hom = p.hom

namespace Factorization

/-- Construct a factorization from a morphism of field spectra together with the two commuting
triangles. -/
def of {p q : FieldValuedPoint X} (schemeHom : p.overObj.left ⟶ q.overObj.left)
    (fac_structure : schemeHom ≫ q.structureHom = p.structureHom)
    (fac_hom : ofOverHomMk schemeHom fac_structure ≫ q.hom = p.hom) :
    Factorization p q where
  schemeHom := schemeHom
  fac_structure := fac_structure
  fac_hom := fac_hom

/-- The identity factorization commutes with the structure morphisms. -/
theorem refl_fac_structure (p : FieldValuedPoint X) :
    (𝟙 p.overObj.left) ≫ p.structureHom = p.structureHom := sorry

/-- The identity factorization commutes with the morphisms into `X`. -/
theorem refl_fac_hom (p : FieldValuedPoint X) :
    ofOverHomMk (𝟙 p.overObj.left) (refl_fac_structure p) ≫ p.hom = p.hom := sorry

/-- The identity factorization of a field-valued point. -/
def refl (p : FieldValuedPoint X) : Factorization p p where
  schemeHom := 𝟙 _
  fac_structure := refl_fac_structure p
  fac_hom := refl_fac_hom p

/-- Postcomposition preserves the structure-morphism triangle of a factorization. -/
theorem map_fac_structure {Y : AlgebraicSpace S} {p q : FieldValuedPoint X}
    (φ : Factorization p q) (f : X ⟶ Y) :
    φ.schemeHom ≫ (q.map f).structureHom = (p.map f).structureHom := sorry

/-- Postcomposition preserves the morphism triangle of a factorization. -/
theorem map_fac_hom {Y : AlgebraicSpace S} {p q : FieldValuedPoint X}
    (φ : Factorization p q) (f : X ⟶ Y) :
    ofOverHomMk φ.schemeHom (map_fac_structure φ f) ≫ (q.map f).hom = (p.map f).hom := sorry

/-- Postcompose a factorization with a morphism of algebraic spaces over `S`. -/
def map {Y : AlgebraicSpace S} {p q : FieldValuedPoint X} (φ : Factorization p q) (f : X ⟶ Y) :
    Factorization (p.map f) (q.map f) where
  schemeHom := φ.schemeHom
  fac_structure := map_fac_structure φ f
  fac_hom := map_fac_hom φ f

/-- A factorization is a morphism of field spectra making both the `S`-triangle and the `X`-triangle
commute. -/
theorem spec {p q : FieldValuedPoint X} (φ : Factorization p q) :
    φ.schemeHom ≫ q.structureHom = p.structureHom ∧
      ofOverHomMk φ.schemeHom φ.fac_structure ≫ q.hom = p.hom := sorry

end Factorization

/-- A common extension of `p` and `q` is a field-valued point dominating both of them. -/
structure CommonExtension (p q : FieldValuedPoint X) where
  /-- The common field-valued extension. -/
  point : FieldValuedPoint X
  /-- Its factorization through `p`. -/
  left : Factorization point p
  /-- Its factorization through `q`. -/
  right : Factorization point q

namespace CommonExtension

/-- Build a common extension from a field-valued point and factorizations through `p` and `q`. -/
def of {p q : FieldValuedPoint X} (point : FieldValuedPoint X) (left : Factorization point p)
    (right : Factorization point q) : CommonExtension p q where
  point := point
  left := left
  right := right

/-- The tautological common extension of a field-valued point with itself. -/
def refl (p : FieldValuedPoint X) : CommonExtension p p where
  point := p
  left := Factorization.refl p
  right := Factorization.refl p

/-- Reverse the two legs of a common extension. -/
def symm {p q : FieldValuedPoint X} (e : CommonExtension p q) : CommonExtension q p where
  point := e.point
  left := e.right
  right := e.left

/-- Postcompose both legs of a common extension with a morphism of algebraic spaces over `S`. -/
def map {Y : AlgebraicSpace S} {p q : FieldValuedPoint X} (e : CommonExtension p q) (f : X ⟶ Y) :
    CommonExtension (p.map f) (q.map f) where
  point := e.point.map f
  left := e.left.map f
  right := e.right.map f

end CommonExtension

/-- Field-valued points are equivalent when they admit a common field-valued extension over `X`. -/
def Equivalent (p q : FieldValuedPoint X) : Prop :=
  Nonempty (CommonExtension p q)

/-- Equivalence of field-valued points is reflexive. -/
theorem Equivalent.refl (p : FieldValuedPoint X) : Equivalent p p :=
  ⟨CommonExtension.refl p⟩

/-- Equivalence of field-valued points is symmetric. -/
theorem Equivalent.symm {p q : FieldValuedPoint X} : Equivalent p q → Equivalent q p := sorry

/-- Equivalence of field-valued points is transitive. -/
theorem Equivalent.trans {p q r : FieldValuedPoint X} :
    Equivalent p q → Equivalent q r → Equivalent p r := sorry

/-- Equivalence is preserved by postcomposition with a morphism of algebraic spaces over `S`. -/
theorem Equivalent.map {Y : AlgebraicSpace S} {p q : FieldValuedPoint X} (h : Equivalent p q)
    (f : X ⟶ Y) : Equivalent (p.map f) (q.map f) := sorry

/-- Equivalence of field-valued points is the existence of a common field spectrum over `S` whose
restrictions recover the two morphisms into `X`. -/
theorem equivalent_iff (p q : FieldValuedPoint X) :
    Equivalent p q ↔
      ∃ (r : FieldValuedPoint X) (i : r.overObj.left ⟶ p.overObj.left)
        (j : r.overObj.left ⟶ q.overObj.left)
        (hi : i ≫ p.structureHom = r.structureHom)
        (hj : j ≫ q.structureHom = r.structureHom),
        ofOverHomMk i hi ≫ p.hom = ofOverHomMk j hj ≫ q.hom := sorry

end FieldValuedPoint

/-- The setoid of field-valued points of an algebraic space, with relation the common-extension
equivalence. -/
def equivalentSetoid {S : Scheme.{u}} (X : AlgebraicSpace S) : Setoid (FieldValuedPoint X) where
  r := FieldValuedPoint.Equivalent
  iseqv := {
    refl := FieldValuedPoint.Equivalent.refl
    symm := FieldValuedPoint.Equivalent.symm
    trans := FieldValuedPoint.Equivalent.trans
  }

/-- The setoid relation is the common-extension equivalence of field-valued points. -/
@[simp]
theorem equivalentSetoid_rel_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (p q : FieldValuedPoint X) :
    equivalentSetoid X p q ↔ FieldValuedPoint.Equivalent p q := sorry

/-- The set of points of an algebraic space, as equivalence classes of morphisms from spectra of
fields. -/
def Points {S : Scheme.{u}} (X : AlgebraicSpace S) : Type (u + 1) :=
  Quotient (equivalentSetoid X)

/-- The set of points of an algebraic space `X`. -/
scoped notation:max "|" X:max "|" => Points X

namespace Points

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The class of a field-valued point. -/
def mk (p : FieldValuedPoint X) : Points X :=
  Quotient.mk (equivalentSetoid X) p

/-- Two field-valued points determine the same point of `X` exactly when they admit a common
field-valued extension. -/
@[simp]
theorem mk_eq_mk_iff (p q : FieldValuedPoint X) :
    mk p = mk q ↔ FieldValuedPoint.Equivalent p q := sorry

/-- The map on points induced by a morphism of algebraic spaces over `S`. -/
def map {Y : AlgebraicSpace S} (f : X ⟶ Y) : Points X → Points Y :=
  Quotient.map (fun p ↦ p.map f) fun _ _ h ↦ FieldValuedPoint.Equivalent.map h f

/-- The induced map on points sends the class of a representative to the class of its
postcomposition. -/
@[simp]
theorem map_mk {Y : AlgebraicSpace S} (f : X ⟶ Y) (p : FieldValuedPoint X) :
    map f (mk p) = mk (p.map f) := sorry

/-- The identity morphism of algebraic spaces induces the identity on points. -/
@[simp]
theorem map_id (x : Points X) : map (𝟙 X) x = x := sorry

/-- The induced map on points preserves composition. -/
@[simp]
theorem map_comp {Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) (x : Points X) :
    map (f ≫ g) x = map g (map f x) := sorry

end Points

end AlgebraicGeometry.AlgebraicSpace
