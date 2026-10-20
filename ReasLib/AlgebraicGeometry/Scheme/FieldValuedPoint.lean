/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.ConnectedComponents
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Field-valued points of a scheme

This file treats the field as part of a field-valued point.  This is the
correct level for comparing points whose source fields need not agree.  The
domination relation is expressed by morphisms in `Over X`, and the canonical
smallest representative is the residue-field point `Spec κ(x) ⟶ X`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme

set_option backward.privateInPublic true in
/-- Explicit source-field and scheme-morphism data for a field-valued point. -/
private structure FieldValuedPointObj (X : Scheme.{u}) where
  /-- The source field. -/
  K : Type u
  /-- The field structure on the source. -/
  [field : Field K]
  /-- The morphism from the field spectrum to the scheme. -/
  hom : Spec (.of K) ⟶ X

set_option backward.privateInPublic true in
/-- Construct explicit field-valued-point data from a field and a scheme morphism. -/
def FieldValuedPointObj.of {X : Scheme.{u}} (K : Type u) [Field K]
    (hom : Spec (.of K) ⟶ X) : FieldValuedPointObj X :=
  ⟨K, hom⟩

set_option backward.privateInPublic true in
/-- The slice object determined by explicit field-valued-point data. -/
private def fieldValuedPointOver {X : Scheme.{u}} (p : FieldValuedPointObj X) :
    Over X :=
  Over.mk p.hom

set_option backward.privateInPublic true in
/-- Field-valued points of `X`, with morphisms induced from the slice category `Over X`. -/
@[stacks 01J9 "field-valued points of a scheme"]
abbrev FieldValuedPoint (X : Scheme.{u}) :=
  InducedCategory (Over X) (fieldValuedPointOver (X := X))

namespace FieldValuedPoint

variable {X : Scheme.{u}}

set_option backward.privateInPublic true in
/-- The source-field carrier of a field-valued point. -/
abbrev K (p : FieldValuedPoint X) : Type u := FieldValuedPointObj.K p

set_option backward.privateInPublic true in
/-- The field structure stored in a field-valued point. -/
abbrev field (p : FieldValuedPoint X) : Field p.K := FieldValuedPointObj.field p

attribute [instance] FieldValuedPoint.field
attribute [stacks 01J9 "field-valued point field structure"] FieldValuedPoint.field
attribute [stacks 01J9 "field-valued point source field"] FieldValuedPoint.K

set_option backward.privateInPublic true in
/-- The morphism from the source-field spectrum of a field-valued point to its scheme. -/
abbrev hom (p : FieldValuedPoint X) : Spec (.of p.K) ⟶ X := FieldValuedPointObj.hom p

attribute [stacks 01J9 "field-valued point scheme morphism"] FieldValuedPoint.hom

set_option backward.privateInPublic true in
/-- Construct a field-valued point from a specified field and spectrum-to-scheme morphism. -/
abbrev of (K : Type u) [Field K] (hom : Spec (.of K) ⟶ X) : FieldValuedPoint X where
  K := K
  hom := hom

/-- A field-valued point regarded as an object of the slice category over
`X`. -/
@[stacks 01J9 "field-valued point over object"]
def over (p : FieldValuedPoint X) : Over X :=
  Over.mk p.hom

/-- The fully faithful functor from field-valued points to the slice over
`X`. -/
@[stacks 01J9 "field-valued points in the slice category"]
def toOver (X : Scheme.{u}) : FieldValuedPoint X ⥤ Over X :=
  inducedFunctor FieldValuedPoint.over

/-- The slice embedding of field-valued points is fully faithful. -/
@[stacks 01J9 "field-valued point slice embedding is fully faithful"]
def toOverFullyFaithful (X : Scheme.{u}) : (toOver X).FullyFaithful :=
  fullyFaithfulInducedFunctor FieldValuedPoint.over

/-- The object map of `toOver` is the explicit slice object. -/
@[simp, stacks 01J9 "field-valued point slice-object readout"]
theorem toOver_obj (p : FieldValuedPoint X) :
    (toOver X).obj p = p.over := sorry

/-- The morphism map of `toOver` is the underlying slice morphism. -/
@[simp, stacks 01J9 "field-valued point slice-morphism readout"]
theorem toOver_map {p q : FieldValuedPoint X} (f : p ⟶ q) :
    (toOver X).map f = f.hom := sorry

/-- Construct a morphism of field-valued points from a map of their source spectra whose
triangle over `X` commutes. -/
@[stacks 01J9 "field-valued point morphism constructor"]
def homMk {p q : FieldValuedPoint X}
    (f : Spec (.of p.K) ⟶ Spec (.of q.K)) (fac : f ≫ q.hom = p.hom) : p ⟶ q :=
  InducedCategory.homMk (Over.homMk f fac)

/-- The map between source field spectra underlying a morphism of field-valued points. -/
@[stacks 01J9 "underlying map of a field-valued point morphism"]
abbrev schemeHom {p q : FieldValuedPoint X} (f : p ⟶ q) :
    Spec (.of p.K) ⟶ Spec (.of q.K) :=
  f.hom.left

/-- The contravariant field homomorphism underlying a morphism of field-valued points. -/
@[stacks 01J9 "underlying field homomorphism of a field-valued point morphism"]
abbrev fieldHom {p q : FieldValuedPoint X} (f : p ⟶ q) :
    CommRingCat.of q.K ⟶ CommRingCat.of p.K :=
  Spec.homEquiv (schemeHom f)

namespace fieldHom

/-- Applying `Spec.map` to the underlying field homomorphism recovers the source-spectrum map. -/
@[simp, stacks 01J9 "field-valued point field-homomorphism spectrum readout"]
theorem specMap {p q : FieldValuedPoint X} (f : p ⟶ q) :
    Spec.map (fieldHom f) = schemeHom f := sorry

/-- The field homomorphism underlying an identity is the identity. -/
@[simp, stacks 01J9 "field-valued point identity field homomorphism"]
theorem id (p : FieldValuedPoint X) : fieldHom (𝟙 p) = 𝟙 (CommRingCat.of p.K) := sorry

/-- Underlying field homomorphisms reverse composition of field-valued-point morphisms. -/
@[simp, stacks 01J9 "field-valued point composite field homomorphism"]
theorem comp {p q r : FieldValuedPoint X} (f : p ⟶ q) (g : q ⟶ r) :
    fieldHom (f ≫ g) = fieldHom g ≫ fieldHom f := sorry

end fieldHom

/-- The morphism constructed by `homMk` has the prescribed underlying scheme map. -/
@[simp, stacks 01J9 "field-valued point morphism constructor readout"]
theorem schemeHom_homMk {p q : FieldValuedPoint X}
    (f : Spec (.of p.K) ⟶ Spec (.of q.K)) (fac : f ≫ q.hom = p.hom) :
    schemeHom (homMk f fac) = f := sorry

/-- The underlying scheme map of a field-valued point morphism commutes with the maps to `X`. -/
@[reassoc, stacks 01J9 "field-valued point morphism triangle"]
theorem schemeHom_fac {p q : FieldValuedPoint X} (f : p ⟶ q) :
    schemeHom f ≫ q.hom = p.hom := sorry

/-- The underlying scheme map of an identity field-valued point morphism is the identity. -/
@[simp, stacks 01J9 "field-valued point identity map"]
theorem schemeHom_id (p : FieldValuedPoint X) :
    schemeHom (𝟙 p) = 𝟙 (Spec (.of p.K)) := sorry

/-- Taking the underlying scheme map preserves composition of field-valued point morphisms. -/
@[simp, stacks 01J9 "field-valued point composition map"]
theorem schemeHom_comp {p q r : FieldValuedPoint X} (f : p ⟶ q) (g : q ⟶ r) :
    schemeHom (f ≫ g) = schemeHom f ≫ schemeHom g := sorry

/-- Morphisms of field-valued points are determined by their maps between source spectra. -/
@[ext, stacks 01J9 "field-valued point morphism extensionality"]
theorem hom_ext {p q : FieldValuedPoint X} {f g : p ⟶ q}
    (h : schemeHom f = schemeHom g) : f = g := sorry

/-- A factorization from `p` to `q` is a morphism between their field spectra
over `X`.  Existence of such a factorization says that `p` dominates `q`. -/
@[stacks 01J9 "field-valued point factorization"]
abbrev Factorization (p q : FieldValuedPoint X) :=
  p ⟶ q

/-- Postcompose a field-valued point with a morphism of schemes. -/
@[stacks 01J9 "postcomposition of a field-valued point"]
def map {Y : Scheme.{u}} (p : FieldValuedPoint X) (g : X ⟶ Y) :
    FieldValuedPoint Y :=
  of p.K (p.hom ≫ g)

/-- Postcomposition by an identity scheme morphism leaves a field-valued point unchanged. -/
@[simp, stacks 01J9 "field-valued point map identity"]
theorem map_id (p : FieldValuedPoint X) :
    p.map (𝟙 X) = p := sorry

/-- Postcomposition of a field-valued point is associative. -/
@[simp, stacks 01J9 "field-valued point map composition"]
theorem map_comp {Y Z : Scheme.{u}} (p : FieldValuedPoint X)
    (g : X ⟶ Y) (h : Y ⟶ Z) :
    p.map (g ≫ h) = (p.map g).map h := sorry

/-- The scheme morphism of a postcomposed field-valued point is the evident composite. -/
@[simp, stacks 01J9 "postcomposed field-valued point scheme-map readout"]
theorem map_hom {Y : Scheme.{u}} (p : FieldValuedPoint X) (g : X ⟶ Y) :
    (p.map g).hom = p.hom ≫ g := sorry

/-- The explicit slice object of a postcomposed point agrees with `Over.map`. -/
@[simp, stacks 01J9 "postcomposed field-valued point slice readout"]
theorem map_over {Y : Scheme.{u}} (p : FieldValuedPoint X) (g : X ⟶ Y) :
    (p.map g).over = (Over.map g).obj p.over := sorry

/-- Postcompose a morphism of field-valued points with a scheme morphism. -/
@[reassoc, stacks 01J9 "postcomposed field-valued point morphism triangle"]
theorem mapHom_fac {Y : Scheme.{u}} (g : X ⟶ Y) {p q : FieldValuedPoint X}
    (f : p ⟶ q) :
    schemeHom f ≫ (q.map g).hom = (p.map g).hom := sorry

/-- Postcompose a morphism of field-valued points with a scheme morphism. -/
@[stacks 01J9 "postcomposition of a field-valued point morphism"]
def mapHom {Y : Scheme.{u}} (g : X ⟶ Y) {p q : FieldValuedPoint X} (f : p ⟶ q) :
    p.map g ⟶ q.map g :=
  InducedCategory.homMk ((Over.map g).map f.hom)

/-- The slice morphism underlying `mapHom` is the canonical `Over.map` image. -/
@[simp, stacks 01J9 "postcomposed field-valued point slice-morphism readout"]
theorem mapHom_hom {Y : Scheme.{u}} (g : X ⟶ Y) {p q : FieldValuedPoint X}
    (f : p ⟶ q) :
    (mapHom g f).hom = (Over.map g).map f.hom := sorry

/-- The underlying source-spectrum map is unchanged by postcomposition. -/
@[simp, stacks 01J9 "postcomposed field-valued point morphism readout"]
theorem schemeHom_mapHom {Y : Scheme.{u}} (g : X ⟶ Y) {p q : FieldValuedPoint X}
    (f : p ⟶ q) :
    schemeHom (mapHom g f) = schemeHom f := sorry

/-- Postcompose a field-valued-point factorization with a scheme morphism. -/
@[stacks 01J9 "postcomposition of a field-valued point factorization"]
def Factorization.map {Y : Scheme.{u}} {p q : FieldValuedPoint X}
    (f : p.Factorization q) (g : X ⟶ Y) : (p.map g).Factorization (q.map g) :=
  mapHom g f

/-- The source-spectrum map of a postcomposed factorization is unchanged. -/
@[simp, stacks 01J9 "postcomposed factorization map readout"]
theorem Factorization.map_hom {Y : Scheme.{u}} {p q : FieldValuedPoint X}
    (f : p.Factorization q) (g : X ⟶ Y) :
    schemeHom (f.map g) = schemeHom f := sorry

/-- Postcomposition sends identity morphisms to identity morphisms. -/
@[simp, stacks 01J9 "postcomposition identity morphism"]
theorem mapHom_id {Y : Scheme.{u}} (g : X ⟶ Y) (p : FieldValuedPoint X) :
    mapHom g (𝟙 p) = 𝟙 (p.map g) := sorry

/-- Postcomposition preserves composition of field-valued point morphisms. -/
@[simp, stacks 01J9 "postcomposition composite morphism"]
theorem mapHom_comp {Y : Scheme.{u}} (g : X ⟶ Y) {p q r : FieldValuedPoint X}
    (f : p ⟶ q) (h : q ⟶ r) :
    mapHom g (f ≫ h) = mapHom g f ≫ mapHom g h := sorry

/-- The functor on field-valued points induced by postcomposition with a scheme morphism. -/
@[stacks 01J9 "postcomposition functor on field-valued points"]
def mapFunctor {Y : Scheme.{u}} (g : X ⟶ Y) :
    FieldValuedPoint X ⥤ FieldValuedPoint Y where
  obj p := p.map g
  map f := mapHom g f
  map_id := mapHom_id g
  map_comp := mapHom_comp g

/-- The object map of the postcomposition functor. -/
@[simp, stacks 01J9 "postcomposition functor object readout"]
theorem mapFunctor_obj {Y : Scheme.{u}} (g : X ⟶ Y) (p : FieldValuedPoint X) :
    (mapFunctor g).obj p = p.map g := sorry

/-- The morphism map of the postcomposition functor. -/
@[simp, stacks 01J9 "postcomposition functor morphism readout"]
theorem mapFunctor_map {Y : Scheme.{u}} (g : X ⟶ Y) {p q : FieldValuedPoint X}
    (f : p ⟶ q) :
    (mapFunctor g).map f = mapHom g f := sorry

/-- Postcomposition is faithful on morphisms of field-valued points. -/
@[stacks 01J9 "postcomposition functor on field-valued points is faithful"]
instance mapFunctor_faithful {Y : Scheme.{u}} (g : X ⟶ Y) :
    (mapFunctor g).Faithful := sorry

namespace mapFunctor

/-- Postcomposition followed by the slice embedding is the restriction of canonical slice
postcomposition. -/
@[simp, stacks 01J9 "postcomposition functor slice comparison"]
theorem comp_toOver {Y : Scheme.{u}} (g : X ⟶ Y) :
    mapFunctor g ⋙ toOver Y = toOver X ⋙ Over.map g := sorry

/-- Postcomposition by an identity morphism is the identity functor on field-valued points. -/
@[stacks 01J9 "identity postcomposition functor"]
theorem mapId_eq (X : Scheme.{u}) :
    mapFunctor (𝟙 X) = 𝟭 (FieldValuedPoint X) := sorry

/-- Postcomposition functors respect composition of scheme morphisms. -/
@[stacks 01J9 "composition of postcomposition functors"]
theorem mapComp_eq {Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z) :
    mapFunctor (g ≫ h) = mapFunctor g ⋙ mapFunctor h := sorry

end mapFunctor

/-- The postcomposition action of schemes on the categories of field-valued points. -/
@[stacks 01J9 "field-valued point action on schemes"]
def action : Scheme.{u} ⥤ Cat.{u, u + 1} where
  obj X := Cat.of (FieldValuedPoint X)
  map g := (mapFunctor g).toCatHom
  map_id X := congr($(mapFunctor.mapId_eq X).toCatHom)
  map_comp g h := congr($(mapFunctor.mapComp_eq g h).toCatHom)

/-- The canonical comparison from the field-valued-point action to the slice action. -/
@[stacks 01J9 "field-valued point action in the slice action"]
def toOverNatTrans : action ⟶ Over.mapFunctor Scheme.{u} where
  app X := (toOver X).toCatHom
  naturality := fun {_ _} g => congr($(mapFunctor.comp_toOver g).toCatHom)

/-- The image in `X` of the unique point of the source field spectrum. -/
@[stacks 01J9 "field-valued point image"]
def image (p : FieldValuedPoint X) : X :=
  p.hom (IsLocalRing.closedPoint p.K)

/-- The image of a postcomposed field-valued point is the image under the scheme morphism. -/
@[simp, stacks 01J9 "image of a postcomposed field-valued point"]
theorem image_map {Y : Scheme.{u}} (p : FieldValuedPoint X) (g : X ⟶ Y) :
    (p.map g).image = g p.image := sorry

/-- A morphism of field-valued points preserves the image in the target scheme. -/
@[stacks 01J9 "field-valued point morphisms preserve image"]
theorem image_eq_of_hom {p q : FieldValuedPoint X} (f : p ⟶ q) :
    p.image = q.image := sorry

/-- The domination relation on field-valued points. -/
@[stacks 01J9 "field-valued point domination"]
def Dominates (p q : FieldValuedPoint X) : Prop :=
  Nonempty (Factorization p q)

/-- Every field-valued point dominates itself. -/
@[refl, stacks 01J9 "field-valued point domination reflexivity"]
theorem Dominates.refl (p : FieldValuedPoint X) : Dominates p p := sorry

/-- Domination of field-valued points is transitive. -/
@[trans, stacks 01J9 "field-valued point domination transitivity"]
theorem Dominates.trans {p q r : FieldValuedPoint X} :
    Dominates p q → Dominates q r → Dominates p r := sorry

/-- Domination implies equality of the image points. -/
@[stacks 01J9 "domination preserves image"]
theorem image_eq_of_dominates {p q : FieldValuedPoint X}
    (h : Dominates p q) : p.image = q.image := sorry

/-- A common extension of `p` and `q` is a field-valued point dominating both
of them. -/
@[stacks 01J9 "common field-valued extension"]
structure CommonExtension (p q : FieldValuedPoint X) where
  /-- The common field-valued extension. -/
  point : FieldValuedPoint X
  /-- Its factorization through `p`. -/
  left : point.Factorization p
  /-- Its factorization through `q`. -/
  right : point.Factorization q

attribute [stacks 01J9 "common field-valued extension point"] CommonExtension.point
attribute [stacks 01J9 "common field-valued extension left leg"] CommonExtension.left
attribute [stacks 01J9 "common field-valued extension right leg"] CommonExtension.right

/-- Build a common extension from a single factorization. -/
@[stacks 01J9 "common extension from a factorization"]
def CommonExtension.ofFactorization {p q : FieldValuedPoint X}
    (f : p.Factorization q) : CommonExtension p q where
  point := p
  left := 𝟙 p
  right := f

/-- A field-valued point is equivalent to another when they have a common
field-valued extension over `X`. -/
@[stacks 01J9 "equivalence of field-valued points"]
def Equivalent (p q : FieldValuedPoint X) : Prop :=
  Nonempty (CommonExtension p q)

/-- A domination exhibits two field-valued points as equivalent. -/
@[stacks 01J9 "domination implies equivalence of field-valued points"]
theorem Dominates.equivalent {p q : FieldValuedPoint X}
    (h : Dominates p q) : Equivalent p q := sorry

/-- The tautological common extension of a field-valued point with itself. -/
@[stacks 01J9 "reflexive common field-valued extension"]
def CommonExtension.refl (p : FieldValuedPoint X) : CommonExtension p p where
  point := p
  left := 𝟙 p
  right := 𝟙 p

/-- Reverse the two legs of a common extension. -/
@[stacks 01J9 "symmetric common field-valued extension"]
def CommonExtension.symm {p q : FieldValuedPoint X}
    (e : CommonExtension p q) : CommonExtension q p where
  point := e.point
  left := e.right
  right := e.left

/-- Postcompose both legs of a common extension with a scheme morphism. -/
@[stacks 01J9 "postcomposition of a common field-valued extension"]
def CommonExtension.map {Y : Scheme.{u}} {p q : FieldValuedPoint X}
    (e : CommonExtension p q) (g : X ⟶ Y) :
    CommonExtension (p.map g) (q.map g) where
  point := e.point.map g
  left := e.left.map g
  right := e.right.map g

/-- The common-extension point is postcomposed componentwise. -/
@[simp, stacks 01J9 "common-extension point postcomposition readout"]
theorem CommonExtension.map_point {Y : Scheme.{u}} {p q : FieldValuedPoint X}
    (e : CommonExtension p q) (g : X ⟶ Y) :
    (e.map g).point = e.point.map g := sorry

/-- The left leg of a postcomposed common extension is the postcomposed left leg. -/
@[simp, stacks 01J9 "common-extension left-leg postcomposition readout"]
theorem CommonExtension.map_left {Y : Scheme.{u}} {p q : FieldValuedPoint X}
    (e : CommonExtension p q) (g : X ⟶ Y) :
    (e.map g).left = e.left.map g := sorry

/-- The right leg of a postcomposed common extension is the postcomposed right leg. -/
@[simp, stacks 01J9 "common-extension right-leg postcomposition readout"]
theorem CommonExtension.map_right {Y : Scheme.{u}} {p q : FieldValuedPoint X}
    (e : CommonExtension p q) (g : X ⟶ Y) :
    (e.map g).right = e.right.map g := sorry

/-- Domination is preserved by postcomposition with a scheme morphism. -/
@[stacks 01J9 "postcomposition preserves field-valued point domination"]
theorem Dominates.map {Y : Scheme.{u}} {p q : FieldValuedPoint X}
    (h : Dominates p q) (g : X ⟶ Y) :
    Dominates (p.map g) (q.map g) := sorry

/-- Equivalence is preserved by postcomposition with a scheme morphism. -/
@[stacks 01J9 "postcomposition preserves field-valued point equivalence"]
theorem Equivalent.map {Y : Scheme.{u}} {p q : FieldValuedPoint X}
    (h : Equivalent p q) (g : X ⟶ Y) :
    Equivalent (p.map g) (q.map g) := sorry

/-- Equivalence of field-valued points is reflexive. -/
@[refl, stacks 01J9 "field-valued point equivalence reflexivity"]
theorem Equivalent.refl (p : FieldValuedPoint X) : Equivalent p p := sorry

/-- Equivalence of field-valued points is symmetric. -/
@[symm, stacks 01J9 "field-valued point equivalence symmetry"]
theorem Equivalent.symm {p q : FieldValuedPoint X} :
    Equivalent p q → Equivalent q p := sorry

/-- Equivalence of field-valued points is transitive. -/
@[trans, stacks 01J9 "field-valued point equivalence transitivity"]
theorem Equivalent.trans {p q r : FieldValuedPoint X} :
    Equivalent p q → Equivalent q r → Equivalent p r := sorry

/-- Common-extension equivalence is the canonical zigzag relation in the category of
field-valued points. -/
@[stacks 01J9 "field-valued point equivalence as a categorical zigzag"]
theorem equivalent_iff_zigzag (p q : FieldValuedPoint X) :
    Equivalent p q ↔ Zigzag p q := sorry

/-- Two field-valued points determine the same Mathlib connected component exactly when they
have a common field-valued extension. -/
@[stacks 01J9 "field-valued point connected-component criterion"]
theorem connectedComponents_mk_eq_iff (p q : FieldValuedPoint X) :
    CategoryTheory.ConnectedComponents.mk p =
      CategoryTheory.ConnectedComponents.mk q ↔ Equivalent p q := sorry

/-- The canonical field-valued point `Spec κ(x) ⟶ X`. -/
@[stacks 01J9 "canonical residue-field point"]
def residuePoint (x : X) : FieldValuedPoint X :=
  of (X.residueField x) (X.fromSpecResidueField x)

/-- The image of the canonical residue-field point is the original point. -/
@[simp, stacks 01J9 "residue-field point image"]
theorem image_residuePoint (x : X) : image (residuePoint x) = x := sorry

/-- The canonical embedding `κ(p.image) ⟶ p.K`. -/
@[stacks 01J9 "residue-field embedding of a field-valued point"]
def residueFieldHom (p : FieldValuedPoint X) :
    X.residueField p.image ⟶ .of p.K :=
  (Scheme.SpecToEquivOfField p.K X p.hom).2

/-- The morphism from a field-valued point to the spectrum of the residue
field of its image. -/
@[stacks 01J9 "field-valued point residue factorization map"]
def toResiduePoint (p : FieldValuedPoint X) :
    Spec (.of p.K) ⟶ Spec (X.residueField p.image) :=
  Spec.map p.residueFieldHom

/-- The canonical residue-field factorization recovers the original
field-valued point. -/
@[reassoc, stacks 01J9 "residue-field factorization computation"]
theorem toResiduePoint_comp (p : FieldValuedPoint X) :
    p.toResiduePoint ≫ (residuePoint p.image).hom = p.hom := sorry

/-- The canonical factorization of a field-valued point through the
residue-field point of its image. -/
@[stacks 01J9 "canonical factorization through the residue-field point"]
def factorToResiduePoint (p : FieldValuedPoint X) :
    p.Factorization (residuePoint p.image) :=
  homMk p.toResiduePoint
    (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField p.K X p.hom)

/-- The canonical factorization of a postcomposed residue-field point through the residue-field
point of its new image. -/
@[reassoc, stacks 01J9 "residue-field point postcomposition factorization"]
theorem residuePoint_map_fac {Y : Scheme.{u}} (g : X ⟶ Y) (x : X) :
    Spec.map (g.residueFieldMap x) ≫ (residuePoint (g x)).hom =
      (residuePoint x).hom ≫ g := sorry

/-- The induced morphism from a postcomposed residue-field point to the residue-field point of its
image. -/
@[stacks 01J9 "residue-field point postcomposition map"]
def residuePoint.mapFactor {Y : Scheme.{u}} (g : X ⟶ Y) (x : X) :
    (residuePoint x).map g ⟶ residuePoint (g x) :=
  homMk (Spec.map (g.residueFieldMap x))
    (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField (f := g) x)

/-- The source-spectrum map of the residue-point postcomposition factorization. -/
@[simp, stacks 01J9 "residue-field point postcomposition map readout"]
theorem schemeHom_mapFactor {Y : Scheme.{u}} (g : X ⟶ Y) (x : X) :
    schemeHom (residuePoint.mapFactor g x) = Spec.map (g.residueFieldMap x) := sorry

namespace factorToResiduePoint

/-- The canonical factorization to a residue-field point is compatible with postcomposition. -/
@[stacks 01J9 "postcomposed residue-field factorization"]
def map {Y : Scheme.{u}} (g : X ⟶ Y) (p : FieldValuedPoint X) :
    p.map g ⟶ residuePoint (g p.image) :=
  mapHom g p.factorToResiduePoint ≫ residuePoint.mapFactor g p.image

/-- The source-spectrum map of the postcomposed canonical residue-field factorization. -/
@[simp, stacks 01J9 "postcomposed residue-field factorization readout"]
theorem schemeHom_map {Y : Scheme.{u}} (g : X ⟶ Y) (p : FieldValuedPoint X) :
    schemeHom (map g p) =
      schemeHom p.factorToResiduePoint ≫ Spec.map (g.residueFieldMap p.image) := sorry

/-- The postcomposed canonical factorization agrees with the canonical factorization of the
postcomposed point, after transporting the target along `image_map`. -/
@[stacks 01J9 "postcomposed residue-field factorization coherence"]
theorem map_eq_factor {Y : Scheme.{u}} (g : X ⟶ Y) (p : FieldValuedPoint X) :
    map g p =
      (p.map g).factorToResiduePoint ≫
        eqToHom (congrArg (residuePoint (X := Y)) (image_map p g)) := sorry

end factorToResiduePoint

/-- The factorization through the residue-field point is unique. -/
@[stacks 01J9 "residue-field factorization uniqueness"]
theorem factorToResiduePoint_unique (p : FieldValuedPoint X)
    (f : p.Factorization (residuePoint p.image)) :
    f = p.factorToResiduePoint := sorry

/-- The object property of having image equal to `x`. -/
@[stacks 01J9 "fixed-image object property"]
def imageFiberProperty (x : X) : ObjectProperty (FieldValuedPoint X) :=
  fun p ↦ p.image = x

/-- The full category of field-valued points whose image is `x`. -/
@[stacks 01J9 "fixed-image category of field-valued points"]
abbrev ImageFiber (x : X) :=
  (imageFiberProperty x).FullSubcategory

/-- Postcomposition sends the image fiber over `x` into the image fiber over `g x`. -/
@[stacks 01J9 "fixed-image fiber reindexing condition"]
theorem imageFiberProperty.map {Y : Scheme.{u}} (g : X ⟶ Y) (x : X) :
    imageFiberProperty x ≤
      (imageFiberProperty (g x)).inverseImage (mapFunctor g) := sorry

/-- Reindex the fixed-image category along a scheme morphism. -/
@[stacks 01J9 "fixed-image fiber reindexing functor"]
def ImageFiber.map {Y : Scheme.{u}} (g : X ⟶ Y) (x : X) :
    ImageFiber x ⥤ ImageFiber (g x) :=
  ObjectProperty.FullSubcategory.restrict (mapFunctor g) (imageFiberProperty.map g x)

/-- The object map of fixed-image fiber reindexing is postcomposition of representatives. -/
@[simp, stacks 01J9 "fixed-image fiber object reindexing readout"]
theorem ImageFiber.map_obj_obj {Y : Scheme.{u}} (g : X ⟶ Y) (x : X)
    (p : ImageFiber x) :
    ((ImageFiber.map g x).obj p).obj = p.obj.map g := sorry

/-- The morphism map of fixed-image fiber reindexing is postcomposition of representatives. -/
@[simp, stacks 01J9 "fixed-image fiber morphism reindexing readout"]
theorem ImageFiber.map_map_hom {Y : Scheme.{u}} (g : X ⟶ Y) (x : X)
    {p q : ImageFiber x} (f : p ⟶ q) :
    ((ImageFiber.map g x).map f).hom = mapHom g f.hom := sorry

/-- A field-valued point as an object of the full category over its own image. -/
@[stacks 01J9 "field-valued point in its image fiber"]
def inImageFiber (p : FieldValuedPoint X) : ImageFiber p.image :=
  ⟨p, rfl⟩

/-- The residue-field point as an object of the fixed-image category. -/
@[stacks 01J9 "residue-field point in the image fiber"]
def residuePointInFiber (x : X) : ImageFiber x :=
  ⟨residuePoint x,
    Scheme.fromSpecResidueField_apply x (IsLocalRing.closedPoint (X.residueField x))⟩

/-- The residue-field factor gives the canonical comparison from the reindexed residue point to
the residue point of `g x`. -/
@[stacks 01J9 "fixed-image residue reindexing factor"]
def ImageFiber.mapResidueFactor {Y : Scheme.{u}} (g : X ⟶ Y) (x : X) :
    (ImageFiber.map g x).obj (residuePointInFiber x) ⟶ residuePointInFiber (g x) :=
  ObjectProperty.homMk (residuePoint.mapFactor g x)

/-- The underlying field-valued-point map of the reindexed residue factor. -/
@[simp, stacks 01J9 "fixed-image residue reindexing factor readout"]
theorem ImageFiber.mapResidueFactor_hom {Y : Scheme.{u}} (g : X ⟶ Y) (x : X) :
    (ImageFiber.mapResidueFactor g x).hom = residuePoint.mapFactor g x := sorry

/-- The canonical morphism from a field-valued point over `x` to the
residue-field point over `x`. -/
@[stacks 01J9 "field-valued point fiber factorization"]
def ImageFiber.factor {x : X} (p : ImageFiber x) :
    p ⟶ residuePointInFiber x :=
  ObjectProperty.homMk
    (p.obj.factorToResiduePoint ≫
      eqToHom (congrArg (residuePoint (X := X)) p.property))

/-- The canonical morphism to the residue-field point in a fixed-image fiber
is unique. -/
@[stacks 01J9 "fixed-image residue factorization uniqueness"]
theorem ImageFiber.factor_unique {x : X} (p : ImageFiber x)
    (f : p ⟶ residuePointInFiber x) : f = ImageFiber.factor p := sorry

/-- The reindexed residue factor is the canonical terminal factor in the target image fiber. -/
@[simp, stacks 01J9 "fixed-image residue reindexing terminal factor"]
theorem ImageFiber.mapResidueFactor_eq_factor {Y : Scheme.{u}} (g : X ⟶ Y) (x : X) :
    ImageFiber.mapResidueFactor g x =
      ImageFiber.factor ((ImageFiber.map g x).obj (residuePointInFiber x)) := sorry

/-- The residue-field point is terminal in the category of field-valued points
with fixed image. -/
@[stacks 01J9 "terminal residue-field point in a fixed-image category"]
def residuePoint_isTerminal (x : X) :
    IsTerminal (residuePointInFiber x) :=
  IsTerminal.ofUniqueHom
    (fun p ↦ ImageFiber.factor p)
    (fun p f ↦ ImageFiber.factor_unique p f)

/-- The canonical isomorphism between two terminal objects in a fixed-image
category. -/
@[stacks 01J9 "canonical isomorphism in an image fiber"]
def ImageFiber.terminalIso {x : X} {p q : ImageFiber x}
    (hp : IsTerminal p) (hq : IsTerminal q) : p ≅ q :=
  hp.uniqueUpToIso hq

/-- Every isomorphism between terminal field-valued points with fixed image is
the canonical one. -/
@[stacks 01J9 "uniqueness of the minimal field-valued representative"]
theorem ImageFiber.terminalIso_unique {x : X} {p q : ImageFiber x}
    (hp : IsTerminal p) (hq : IsTerminal q) (e : p ≅ q) :
    e = ImageFiber.terminalIso hp hq := sorry

/-- A smallest representative is dominated by every equivalent field-valued
point. -/
@[stacks 01J9 "smallest field-valued representative"]
def IsSmallest (q : FieldValuedPoint X) : Prop :=
  ∀ p, Equivalent p q → Dominates p q

/-- A terminal representative admits a unique factorization from every field-valued point with
the same image. The data-bearing categorical owner remains the explicit term
`IsTerminal q.inImageFiber`; this predicate does not hide such a certificate. -/
@[stacks 01J9 "terminal field-valued representative"]
def IsTerminalRepresentative (q : FieldValuedPoint X) : Prop :=
  ∀ p : FieldValuedPoint X, p.image = q.image →
    Nonempty (p.Factorization q) ∧ Subsingleton (p.Factorization q)

/-- A field-valued point is a terminal representative exactly when its fixed-image object admits
a terminality certificate. This is a proposition-level characterization; concrete isomorphisms
are obtained from `ImageFiber.terminalIso` after fixing the image fiber explicitly. -/
@[stacks 01J9 "terminal-representative categorical criterion"]
theorem isTerminalRepresentative_iff (q : FieldValuedPoint X) :
    IsTerminalRepresentative q ↔ Nonempty (IsTerminal q.inImageFiber) := sorry

/-- Reusable consequence: the residue-field point is a smallest representative of its
equivalence class. -/
@[stacks 01J9 "minimal residue-field representative"]
theorem residuePoint_isSmallest (x : X) : IsSmallest (residuePoint x) := sorry

/-- The residue-field point is terminal among the representatives of its
equivalence class. -/
@[stacks 01J9 "source-facing terminal residue-field representative"]
theorem residuePoint_isTerminalRepresentative (x : X) :
    IsTerminalRepresentative (residuePoint x) := sorry

/-- Every terminal representative is a smallest representative. -/
@[stacks 01J9 "terminal representative is smallest"]
theorem IsTerminalRepresentative.isSmallest {q : FieldValuedPoint X}
    (hq : IsTerminalRepresentative q) : IsSmallest q := sorry

/-- Two field-valued points are equivalent exactly when they have the same
image in `X`. -/
@[stacks 01J9 "classification of equivalent field-valued points"]
theorem equivalent_iff_image_eq (p q : FieldValuedPoint X) :
    Equivalent p q ↔ p.image = q.image := sorry

/-- Equivalence after postcomposition is equality of the postcomposed images. -/
@[simp, stacks 01J9 "postcomposed field-valued point equivalence criterion"]
theorem equivalent_map_iff {Y : Scheme.{u}} (g : X ⟶ Y)
    (p q : FieldValuedPoint X) :
    Equivalent (p.map g) (q.map g) ↔ g p.image = g q.image := sorry

/-- The kernel-of-image presentation of equivalence classes of field-valued points. Keeping the
classification invariant as the setoid relation makes the quotient representation independent of
the particular common-extension witness used to define `Equivalent`. -/
@[stacks 01J9 "field-valued point image setoid"]
def equivalentSetoid (X : Scheme.{u}) : Setoid (FieldValuedPoint X) :=
  Setoid.ker (image : FieldValuedPoint X → X)

/-- A field-valued point is a smallest representative exactly when every point with the same
image admits a factorization to it. -/
@[stacks 01J9 "smallest-representative factorization criterion"]
theorem isSmallest_iff (q : FieldValuedPoint X) :
    IsSmallest q ↔
      ∀ p : FieldValuedPoint X, p.image = q.image →
        Nonempty (p.Factorization q) := sorry

/-- A smallest field-valued representative is terminal in its fixed-image
category; factorization existence therefore already forces uniqueness. -/
@[stacks 01J9 "smallest representative is terminal"]
theorem IsSmallest.isTerminalRepresentative {q : FieldValuedPoint X}
    (hq : IsSmallest q) : IsTerminalRepresentative q := sorry

/-- Being smallest in the domination relation is equivalent to being terminal
among field-valued points with the same image. -/
@[stacks 01J9 "smallest representatives as terminal objects"]
theorem isSmallest_iff_isTerminalRepresentative (q : FieldValuedPoint X) :
    IsSmallest q ↔ IsTerminalRepresentative q := sorry

/-- Reusable companion: equivalent smallest field-valued representatives are uniquely isomorphic
over `X`. -/
@[stacks 01J9 "uniqueness of smallest field-valued representatives"]
theorem iso_unique_of_isSmallest {p q : FieldValuedPoint X}
    (hp : IsSmallest p) (hq : IsSmallest q) (hpq : Equivalent p q) :
    Nonempty (p ≅ q) ∧ Subsingleton (p ≅ q) := sorry

/-- Equivalent field-valued points have the same image. -/
@[stacks 01J9 "equivalent field-valued points have equal image"]
theorem image_eq_of_equivalent {p q : FieldValuedPoint X}
    (h : Equivalent p q) : p.image = q.image := sorry

/-- The kernel setoid records exactly the textbook common-extension
equivalence relation. -/
@[stacks 01J9 "field-valued point setoid specification"]
theorem equivalentSetoid_rel_iff (p q : FieldValuedPoint X) :
    equivalentSetoid X p q ↔ Equivalent p q := sorry

/-- The kernel-setoid relation is equality of the image points. -/
@[simp, stacks 01J9 "field-valued point image-setoid criterion"]
theorem equivalentSetoid_rel_iff_image_eq (p q : FieldValuedPoint X) :
    equivalentSetoid X p q ↔ p.image = q.image := sorry

/-- Equivalence classes of field-valued points of `X`, represented canonically
as the quotient by equality of images. -/
@[stacks 01J9 "field-valued point classes"]
abbrev Classes (X : Scheme.{u}) :=
  Quotient (equivalentSetoid X)

/-- Send an equivalence class of field-valued points to its image in `X`. -/
@[stacks 01J9 "field-valued point class projection"]
def classToPoint (X : Scheme.{u}) : Classes X → X :=
  Setoid.kerLift (fun p : FieldValuedPoint X ↦ p.image)

/-- Send a point to the class of its canonical residue-field point. -/
@[stacks 01J9 "point to field-valued point class"]
def pointToClass (x : X) : Classes X :=
  Quotient.mk (equivalentSetoid X) (residuePoint x)

/-- Two representatives define the same field-valued-point class exactly when they admit a
common field-valued extension. -/
@[simp, stacks 01J9 "equality of field-valued point classes"]
theorem classes_mk_eq_mk_iff (p q : FieldValuedPoint X) :
    Quotient.mk (equivalentSetoid X) p = Quotient.mk (equivalentSetoid X) q ↔
      Equivalent p q := sorry

/-- Postcomposition preserves the kernel-setoid relation on field-valued points. -/
@[stacks 01J9 "postcomposition preserves the field-valued point setoid"]
theorem Classes.map_congr {Y : Scheme.{u}} (g : X ⟶ Y)
    {p q : FieldValuedPoint X} (h : equivalentSetoid X p q) :
    Quotient.mk (equivalentSetoid Y) (p.map g) =
      Quotient.mk (equivalentSetoid Y) (q.map g) := sorry

/-- The map on equivalence classes induced by postcomposition. It is defined through the canonical
image/class presentation, so it does not choose a representative or hide a well-definedness proof
inside the data. -/
@[stacks 01J9 "postcomposition on field-valued point classes"]
def Classes.map {Y : Scheme.{u}} (g : X ⟶ Y) : Classes X → Classes Y :=
  fun q => pointToClass (g (classToPoint X q))

/-- The class map sends a representative to the class of its postcomposition. -/
@[simp, stacks 01J9 "field-valued point class map representative readout"]
theorem Classes.map_mk {Y : Scheme.{u}} (g : X ⟶ Y) (p : FieldValuedPoint X) :
    Classes.map g (Quotient.mk (equivalentSetoid X) p) =
      Quotient.mk (equivalentSetoid Y) (p.map g) := sorry

/-- Postcomposition by an identity scheme morphism leaves a class unchanged. -/
@[simp, stacks 01J9 "field-valued point class map identity"]
theorem Classes.map_id (q : Classes X) :
    Classes.map (𝟙 X) q = q := sorry

/-- The induced map on classes is associative under postcomposition. -/
@[simp, stacks 01J9 "field-valued point class map composition"]
theorem Classes.map_comp {Y Z : Scheme.{u}} (q : Classes X)
    (g : X ⟶ Y) (h : Y ⟶ Z) :
    Classes.map (g ≫ h) q = Classes.map h (Classes.map g q) := sorry

/-- The class projection commutes with postcomposition by a scheme morphism. -/
@[simp, stacks 01J9 "field-valued class projection naturality"]
theorem classToPoint_map {Y : Scheme.{u}} (g : X ⟶ Y) (q : Classes X) :
    classToPoint Y (Classes.map g q) = g (classToPoint X q) := sorry

/-- The class of a residue-field point is compatible with postcomposition. -/
@[simp, stacks 01J9 "residue-field class map naturality"]
theorem pointToClass_map {Y : Scheme.{u}} (g : X ⟶ Y) (x : X) :
    Classes.map g (pointToClass x) = pointToClass (g x) := sorry

/-- Passing from a point to its residue-field class and back is the identity. -/
@[simp, stacks 01J9 "field-valued class projection left inverse"]
theorem classToPoint_pointToClass (x : X) :
    classToPoint X (pointToClass x) = x := sorry

/-- Every class is represented by the residue-field point of its image. -/
@[simp, stacks 01J9 "field-valued class projection right inverse"]
theorem pointToClass_classToPoint (q : Classes X) :
    pointToClass (classToPoint X q) = q := sorry

/-- Reusable variable-field classification: points of `X` are canonically equivalent to
equivalence classes of field-valued points of `X`. -/
@[stacks 01J9 "points as classes of field-valued points"]
def classesEquiv (X : Scheme.{u}) : Classes X ≃ X :=
  Setoid.quotientKerEquivOfRightInverse
    (f := fun p : FieldValuedPoint X ↦ p.image) residuePoint
    (fun x => Scheme.fromSpecResidueField_apply x
      (IsLocalRing.closedPoint (X.residueField x)))

/-- The forward map of `classesEquiv` sends a class to the common image of its
representatives. -/
@[simp, stacks 01J9 "field-valued point class equivalence forward map"]
theorem classesEquiv_apply (q : Classes X) :
    classesEquiv X q = classToPoint X q := sorry

/-- The inverse map of `classesEquiv` sends a point to the class of its residue-field
representative. -/
@[simp, stacks 01J9 "field-valued point class equivalence inverse map"]
theorem classesEquiv_symm_apply (x : X) :
    (classesEquiv X).symm x = pointToClass x := sorry

/-- The canonical class equivalence is natural under postcomposition. -/
@[simp, stacks 01J9 "field-valued class equivalence naturality"]
theorem classesEquiv_naturality {Y : Scheme.{u}} (g : X ⟶ Y) (q : Classes X) :
    classesEquiv Y (Classes.map g q) = g (classesEquiv X q) := sorry

end FieldValuedPoint

end AlgebraicGeometry.Scheme
