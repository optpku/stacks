/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Equivalence
public import ReasLib.AlgebraicTopology.SimplicialObject.CartesianOver

/-!
# Degeneracy-and-cocycle data for cartesian simplicial objects

Pairs `(V, φ)` consisting of an object over `X _⦋0⦌` and an isomorphism over `X _⦋1⦌`
between the two face pullbacks, together with the degeneracy and `X _⦋2⦌` cocycle laws.
-/

@[expose] public section

open CategoryTheory Limits Opposite
open scoped Simplicial

noncomputable section

universe v u

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable (X : SimplicialObject C)

set_option backward.privateInPublic true in
/-- Reidentify `Over.pullback` along an equality of base morphisms. -/
private def recodePullback {A B : C} {f g : A ⟶ B} (h : f = g) :
    Over.pullback f ≅ Over.pullback g :=
  CategoryTheory.eqToIso (congrArg (fun t ↦ Over.pullback t) h)

set_option backward.privateInPublic true in
/-- Pullback of an over-object along `X.σ 0 ≫ X.δ 1`, transported to an endomorphism of `V`. -/
def degeneracyPullback {V : Over (X _⦋0⦌)}
    (φ : (Over.pullback (X.δ (1 : Fin 2))).obj V ≅
      (Over.pullback (X.δ (0 : Fin 2))).obj V) :
    V ⟶ V :=
  (Over.pullbackId : Over.pullback (𝟙 (X _⦋0⦌)) ≅ 𝟭 _).inv.app V ≫
    (recodePullback (X.δ_comp_σ_succ (i := 0))).inv.app V ≫
    (Over.pullbackComp (X.σ 0) (X.δ (1 : Fin 2))).hom.app V ≫
    (Over.pullback (X.σ 0)).map φ.hom ≫
    (Over.pullbackComp (X.σ 0) (X.δ (0 : Fin 2))).inv.app V ≫
    (recodePullback (X.δ_comp_σ_self (i := 0))).hom.app V ≫
    (Over.pullbackId : Over.pullback (𝟙 (X _⦋0⦌)) ≅ 𝟭 _).hom.app V

/-- The pullback of `φ` along a 2-face `X.δ i`, as a morphism over `X _⦋2⦌`. -/
def facePullback (i : Fin 3) {V : Over (X _⦋0⦌)}
    (φ : (Over.pullback (X.δ (1 : Fin 2))).obj V ≅
      (Over.pullback (X.δ (0 : Fin 2))).obj V) :
    (Over.pullback (X.δ i ≫ X.δ (1 : Fin 2))).obj V ⟶
      (Over.pullback (X.δ i ≫ X.δ (0 : Fin 2))).obj V :=
  (Over.pullbackComp (X.δ i) (X.δ (1 : Fin 2))).hom.app V ≫
    (Over.pullback (X.δ i)).map φ.hom ≫
    (Over.pullbackComp (X.δ i) (X.δ (0 : Fin 2))).inv.app V

/-- The source of the `X _⦋2⦌` cocycle, namely the pullback of `V` along `X.δ 2 ≫ X.δ 1`. -/
abbrev cocycleSource (V : Over (X _⦋0⦌)) : Over (X _⦋2⦌) :=
  (Over.pullback (X.δ (2 : Fin 3) ≫ X.δ (1 : Fin 2))).obj V

/-- The target of the `X _⦋2⦌` cocycle, namely the pullback of `V` along `X.δ 1 ≫ X.δ 0`. -/
abbrev cocycleTarget (V : Over (X _⦋0⦌)) : Over (X _⦋2⦌) :=
  (Over.pullback (X.δ (1 : Fin 3) ≫ X.δ (0 : Fin 2))).obj V

set_option backward.privateInPublic true in
/-- `(X.δ 1)*φ` transported to a morphism `cocycleSource V ⟶ cocycleTarget V`. -/
def cocycleLeft {V : Over (X _⦋0⦌)}
    (φ : (Over.pullback (X.δ (1 : Fin 2))).obj V ≅
      (Over.pullback (X.δ (0 : Fin 2))).obj V) :
    cocycleSource X V ⟶ cocycleTarget X V :=
  (recodePullback (X.δ_comp_δ_self (i := (1 : Fin 2))).symm).hom.app V ≫
    facePullback X 1 φ

set_option backward.privateInPublic true in
/-- `(X.δ 0)*φ ∘ (X.δ 2)*φ` transported to a morphism `cocycleSource V ⟶ cocycleTarget V`. -/
def cocycleRight {V : Over (X _⦋0⦌)}
    (φ : (Over.pullback (X.δ (1 : Fin 2))).obj V ≅
      (Over.pullback (X.δ (0 : Fin 2))).obj V) :
    cocycleSource X V ⟶ cocycleTarget X V :=
  facePullback X 2 φ ≫
    (recodePullback
      (X.δ_comp_δ (i := (0 : Fin 2)) (j := (1 : Fin 2)) (Fin.zero_le _))).hom.app V ≫
    facePullback X 0 φ ≫
    (recodePullback
      (X.δ_comp_δ (i := (0 : Fin 2)) (j := (0 : Fin 2)) le_rfl).symm).hom.app V

/-- Degree-zero objects with a face-pullback isomorphism satisfying degeneracy and cocycle. -/
def CartesianDatum :=
  { datum : (V : Over (X _⦋0⦌)) ×
      ((Over.pullback (X.δ (1 : Fin 2))).obj V ≅
        (Over.pullback (X.δ (0 : Fin 2))).obj V) //
    degeneracyPullback X datum.2 = 𝟙 datum.1 ∧
      cocycleLeft X datum.2 = cocycleRight X datum.2 }

namespace CartesianDatum

variable {X}

/-- The underlying object over degree zero of a descent datum. -/
def schemeOver (D : CartesianDatum X) : Over (X _⦋0⦌) := D.val.1

/-- The isomorphism from the first-face pullback to the zeroth-face pullback. -/
def iso (D : CartesianDatum X) :
    (Over.pullback (X.δ (1 : Fin 2))).obj D.schemeOver ≅
      (Over.pullback (X.δ (0 : Fin 2))).obj D.schemeOver := D.val.2

/-- The face comparison restricts to the identity along the zeroth degeneracy. -/
def degeneracy (D : CartesianDatum X) :
    degeneracyPullback X D.iso = 𝟙 D.schemeOver := D.property.1

/-- The face comparison satisfies the degree-two cocycle equation. -/
def cocycle (D : CartesianDatum X) :
    cocycleLeft X D.iso = cocycleRight X D.iso := D.property.2

/-- Construct descent data from an object, a face isomorphism and its two laws. -/
def ofPullbackIso (V : Over (X _⦋0⦌))
    (e : (Over.pullback (X.δ (1 : Fin 2))).obj V ≅
      (Over.pullback (X.δ (0 : Fin 2))).obj V)
    (hdeg : degeneracyPullback X e = 𝟙 V)
    (hcyc : cocycleLeft X e = cocycleRight X e) : CartesianDatum X :=
  ⟨⟨V, e⟩, hdeg, hcyc⟩

/-- The defining degeneracy and cocycle laws of a descent datum. -/
theorem spec (D : CartesianDatum X) :
    degeneracyPullback X D.iso = 𝟙 D.schemeOver ∧
      cocycleLeft X D.iso = cocycleRight X D.iso := sorry

/-- Morphisms of descent data are over-maps commuting with the face isomorphisms. -/
def Hom (D E : CartesianDatum X) :=
  { left : D.schemeOver ⟶ E.schemeOver //
    (Over.pullback (X.δ (1 : Fin 2))).map left ≫ E.iso.hom =
      D.iso.hom ≫ (Over.pullback (X.δ (0 : Fin 2))).map left }

/-- The underlying over-map of a morphism of descent data. -/
def Hom.left {D E : CartesianDatum X} (f : Hom D E) :
    D.schemeOver ⟶ E.schemeOver := f.val

/-- The underlying over-map commutes with the face isomorphisms. -/
def Hom.comm {D E : CartesianDatum X} (f : Hom D E) :
    (Over.pullback (X.δ (1 : Fin 2))).map f.left ≫ E.iso.hom =
      D.iso.hom ≫ (Over.pullback (X.δ (0 : Fin 2))).map f.left := f.property

/-- Construct a morphism of descent data from a compatible over-map. -/
def homMk {D E : CartesianDatum X} (left : D.schemeOver ⟶ E.schemeOver)
    (comm : (Over.pullback (X.δ (1 : Fin 2))).map left ≫ E.iso.hom =
      D.iso.hom ≫ (Over.pullback (X.δ (0 : Fin 2))).map left) : Hom D E :=
  ⟨left, comm⟩

/-- Identity over-maps commute with the face isomorphism. -/
theorem Hom.id_comm (D : CartesianDatum X) :
    (Over.pullback (X.δ (1 : Fin 2))).map (𝟙 D.schemeOver) ≫ D.iso.hom =
      D.iso.hom ≫ (Over.pullback (X.δ (0 : Fin 2))).map (𝟙 D.schemeOver) := sorry

/-- The identity morphism of descent data. -/
def Hom.id (D : CartesianDatum X) : Hom D D :=
  homMk (𝟙 D.schemeOver) (Hom.id_comm D)

/-- Composites of compatible over-maps commute with the face isomorphisms. -/
theorem Hom.comp_comm {D E F : CartesianDatum X} (f : Hom D E) (g : Hom E F) :
    (Over.pullback (X.δ (1 : Fin 2))).map (f.left ≫ g.left) ≫ F.iso.hom =
      D.iso.hom ≫ (Over.pullback (X.δ (0 : Fin 2))).map (f.left ≫ g.left) := sorry

/-- Composition of morphisms of descent data. -/
def Hom.comp {D E F : CartesianDatum X} (f : Hom D E) (g : Hom E F) : Hom D F :=
  homMk (f.left ≫ g.left) (Hom.comp_comm f g)

/-- The underlying map of a constructed descent morphism is its supplied over-map. -/
theorem homMk_left {D E : CartesianDatum X} (left : D.schemeOver ⟶ E.schemeOver)
    (comm : (Over.pullback (X.δ (1 : Fin 2))).map left ≫ E.iso.hom =
      D.iso.hom ≫ (Over.pullback (X.δ (0 : Fin 2))).map left) :
    (homMk left comm).left = left := sorry

/-- Identity is a left unit for descent morphism composition. -/
theorem Hom.id_comp {D E : CartesianDatum X} (f : Hom D E) :
    Hom.comp (Hom.id D) f = f := sorry

/-- Identity is a right unit for descent morphism composition. -/
theorem Hom.comp_id {D E : CartesianDatum X} (f : Hom D E) :
    Hom.comp f (Hom.id E) = f := sorry

/-- Composition of descent morphisms is associative. -/
theorem Hom.assoc {D E F G : CartesianDatum X}
    (f : Hom D E) (g : Hom E F) (h : Hom F G) :
    Hom.comp (Hom.comp f g) h = Hom.comp f (Hom.comp g h) := sorry

/-- The category of degree-zero objects with compatible face isomorphisms. -/
instance category : Category.{v} (CartesianDatum X) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

/-- The last-vertex operator `X(τ^n_n) : X.obj (op n) ⟶ X _⦋0⦌`. -/
def vertexMap (n : SimplexCategory) : X.obj (op n) ⟶ X _⦋0⦌ :=
  X.map (SimplexCategory.const ⦋0⦌ n (Fin.last n.len)).op

/-- The edge operator `X(τ^m_{β(n)m}) : X.obj (op m) ⟶ X _⦋1⦌`. -/
def edgeMap {n m : SimplexCategory} (β : n ⟶ m) : X.obj (op m) ⟶ X _⦋1⦌ :=
  X.map (SimplexCategory.mkOfLe (β.toOrderHom (Fin.last n.len)) (Fin.last m.len)
      (Fin.le_last _)).op

/-- The reconstructed degree-`n` object `X_n ×_{X(τ^n_n)} V`. -/
abbrev objAt (D : CartesianDatum X) (n : SimplexCategoryᵒᵖ) : C :=
  pullback (vertexMap n.unop) D.schemeOver.hom

/-- Commutativity witness for the map from `objAt D (op m)` into the `δ 0` face pullback. -/
theorem toFace_w (D : CartesianDatum X) {n m : SimplexCategory} (β : n ⟶ m) :
    pullback.snd (vertexMap m) D.schemeOver.hom ≫ D.schemeOver.hom =
      (pullback.fst (vertexMap m) D.schemeOver.hom ≫ edgeMap β) ≫
        X.δ (0 : Fin 2) := sorry

/-- The comparison `Y_m ⟶ V ×_{X_0, X.δ 0} X_1` used to apply `φ.inv`. -/
def toFace (D : CartesianDatum X) {n m : SimplexCategory} (β : n ⟶ m) :
    objAt D (op m) ⟶ ((Over.pullback (X.δ (0 : Fin 2))).obj D.schemeOver).left :=
  pullback.lift (pullback.snd _ _) (pullback.fst _ _ ≫ edgeMap β) (toFace_w D β)

/-- `toFace` projects to `V` by `pullback.snd`. -/
theorem toFace_fst (D : CartesianDatum X) {n m : SimplexCategory} (β : n ⟶ m) :
    toFace D β ≫ pullback.fst D.schemeOver.hom (X.δ (0 : Fin 2)) =
      pullback.snd (vertexMap m) D.schemeOver.hom := sorry

/-- Commutativity witness for the reconstructed simplicial operator `Y(β)`. -/
theorem mapSimplex_w (D : CartesianDatum X) {n m : SimplexCategory} (β : n ⟶ m) :
    (pullback.fst (vertexMap m) D.schemeOver.hom ≫ X.map β.op) ≫
        vertexMap n =
      (toFace D β ≫ D.iso.inv.left ≫ pullback.fst D.schemeOver.hom (X.δ (1 : Fin 2))) ≫
        D.schemeOver.hom := sorry

/-- The reconstructed operator `Y(β) : Y_m ⟶ Y_n`, as the pullback of `φ.inv` along
`X(τ^m_{β(n)m})` followed by projection to `Y_n`. -/
def mapSimplex (D : CartesianDatum X) {n m : SimplexCategory} (β : n ⟶ m) :
    objAt D (op m) ⟶ objAt D (op n) :=
  pullback.lift (pullback.fst _ _ ≫ X.map β.op)
    (toFace D β ≫ D.iso.inv.left ≫ pullback.fst _ _) (mapSimplex_w D β)

/-- `mapSimplex` projects to `X_n` by `X.map β.op`. -/
theorem mapSimplex_fst (D : CartesianDatum X) {n m : SimplexCategory} (β : n ⟶ m) :
    mapSimplex D β ≫ pullback.fst (vertexMap n) D.schemeOver.hom =
      pullback.fst (vertexMap m) D.schemeOver.hom ≫ X.map β.op := sorry

/-- Reconstruction sends the identity simplex operator to the identity. -/
theorem mapSimplex_id (D : CartesianDatum X) (n : SimplexCategoryᵒᵖ) :
    mapSimplex D (𝟙 n).unop = 𝟙 (objAt D n) := sorry

/-- Reconstruction respects contravariant composition of simplex operators. -/
theorem mapSimplex_comp (D : CartesianDatum X) {n m k : SimplexCategoryᵒᵖ}
    (f : n ⟶ m) (g : m ⟶ k) :
    mapSimplex D (f ≫ g).unop = mapSimplex D f.unop ≫ mapSimplex D g.unop := sorry

/-- The reconstructed simplicial object has last-vertex pullbacks as its degrees. -/
def ofDatumObj (D : CartesianDatum X) : SimplicialObject C where
  obj n := objAt D n
  map f := mapSimplex D f.unop
  map_id := mapSimplex_id D
  map_comp := mapSimplex_comp D

/-- Each reconstructed degree is the pullback along its last vertex. -/
theorem ofDatumObj_obj (D : CartesianDatum X) (n : SimplexCategoryᵒᵖ) :
    (ofDatumObj D).obj n = objAt D n := sorry

/-- The last-vertex pullback projections form a natural transformation. -/
theorem ofDatumHom_naturality (D : CartesianDatum X) {n m : SimplexCategoryᵒᵖ}
    (f : n ⟶ m) :
    (ofDatumObj D).map f ≫ pullback.fst (vertexMap m.unop) D.schemeOver.hom =
      pullback.fst (vertexMap n.unop) D.schemeOver.hom ≫ X.map f := sorry

/-- The reconstructed structure morphism has pullback projections as components. -/
def ofDatumHom (D : CartesianDatum X) : ofDatumObj D ⟶ X where
  app n := pullback.fst (vertexMap n.unop) D.schemeOver.hom
  naturality := fun {_ _} β ↦ ofDatumHom_naturality D β

/-- Components of the reconstructed structure morphism are the base projections. -/
theorem ofDatumHom_app (D : CartesianDatum X) (n : SimplexCategoryᵒᵖ) :
    (ofDatumHom D).app n = pullback.fst (vertexMap n.unop) D.schemeOver.hom := sorry

/-- The reconstructed structure morphism is cartesian for every simplex operator. -/
theorem ofDatumHom_isCartesian (D : CartesianDatum X) : IsCartesian (ofDatumHom D) := sorry

/-- The reconstruction bundled as an object cartesian over the simplicial base. -/
def ofDatumObjOver (D : CartesianDatum X) : CartesianOver X :=
  CartesianOver.ofHom (ofDatumHom D) (ofDatumHom_isCartesian D)

/-- A compatible over-map gives a commutative square on last-vertex pullbacks. -/
theorem ofDatumMap_w {D E : CartesianDatum X} (f : D ⟶ E) (n : SimplexCategoryᵒᵖ) :
    pullback.fst (vertexMap n.unop) D.schemeOver.hom ≫ vertexMap n.unop =
      (pullback.snd (vertexMap n.unop) D.schemeOver.hom ≫ f.left.left) ≫
        E.schemeOver.hom := sorry

/-- The degreewise reconstructed map is the canonical lift of the given over-map. -/
def ofDatumMapApp {D E : CartesianDatum X} (f : D ⟶ E) (n : SimplexCategoryᵒᵖ) :
    (ofDatumObj D).obj n ⟶ (ofDatumObj E).obj n :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ f.left.left) (ofDatumMap_w f n)

/-- The degreewise reconstructed maps are natural in simplex operators. -/
theorem ofDatumMap_naturality {D E : CartesianDatum X} (f : D ⟶ E)
    {n m : SimplexCategoryᵒᵖ} (β : n ⟶ m) :
    (ofDatumObj D).map β ≫ ofDatumMapApp f m =
      ofDatumMapApp f n ≫ (ofDatumObj E).map β := sorry

/-- A compatible over-map reconstructs to a map of simplicial objects. -/
def ofDatumMap {D E : CartesianDatum X} (f : D ⟶ E) : ofDatumObj D ⟶ ofDatumObj E where
  app := ofDatumMapApp f
  naturality := fun {_ _} β ↦ ofDatumMap_naturality f β

/-- The reconstructed map lies over the identity of the simplicial base. -/
theorem ofDatumMap_over {D E : CartesianDatum X} (f : D ⟶ E) :
    ofDatumMap f ≫ ofDatumHom E = ofDatumHom D := sorry

/-- Reconstruction of the identity descent morphism is the identity over-map. -/
theorem ofDatum_map_id (D : CartesianDatum X) :
    (InducedCategory.homMk (Over.homMk (ofDatumMap (𝟙 D)) (ofDatumMap_over (𝟙 D))) :
      ofDatumObjOver D ⟶ ofDatumObjOver D) = 𝟙 (ofDatumObjOver D) := sorry

/-- Reconstruction preserves composition of descent morphisms. -/
theorem ofDatum_map_comp {D E F : CartesianDatum X} (f : D ⟶ E) (g : E ⟶ F) :
    (InducedCategory.homMk (Over.homMk (ofDatumMap (f ≫ g)) (ofDatumMap_over (f ≫ g))) :
      ofDatumObjOver D ⟶ ofDatumObjOver F) =
      (InducedCategory.homMk (Over.homMk (ofDatumMap f) (ofDatumMap_over f)) :
        ofDatumObjOver D ⟶ ofDatumObjOver E) ≫
      (InducedCategory.homMk (Over.homMk (ofDatumMap g) (ofDatumMap_over g)) :
        ofDatumObjOver E ⟶ ofDatumObjOver F) := sorry

/-- The functor reconstructing cartesian simplicial objects from descent data. -/
def ofDatum : CartesianDatum X ⥤ CartesianOver X where
  obj := ofDatumObjOver
  map f := InducedCategory.homMk (Over.homMk (ofDatumMap f) (ofDatumMap_over f))
  map_id := ofDatum_map_id
  map_comp := ofDatum_map_comp

/-- The reconstruction functor has the stated object assignment. -/
theorem ofDatum_obj (D : CartesianDatum X) :
    ofDatum.obj D = ofDatumObjOver D := sorry

/-- The canonical face-square comparison is a morphism over degree one. -/
theorem cartesianFaceIso_over {Y : SimplicialObject C} (a : Y ⟶ X)
    (ha : IsCartesian a) (i : Fin 2) :
    (pullbackSymmetry (a.app (op ⦋0⦌)) (X.δ i) ≪≫
      (ha.isPullback (SimplexCategory.δ i)).isoPullback.symm).hom ≫ a.app (op ⦋1⦌) =
      ((Over.pullback (X.δ i)).obj (Over.mk (a.app (op ⦋0⦌)))).hom := sorry

/-- The canonical face comparison of a cartesian morphism is an isomorphism over degree one. -/
def cartesianFaceIso {Y : SimplicialObject C} (a : Y ⟶ X) (ha : IsCartesian a) (i : Fin 2) :
    (Over.pullback (X.δ i)).obj (Over.mk (a.app (op ⦋0⦌))) ≅ Over.mk (a.app (op ⦋1⦌)) :=
  Over.isoMk (pullbackSymmetry (a.app (op ⦋0⦌)) (X.δ i) ≪≫
    (ha.isPullback (SimplexCategory.δ i)).isoPullback.symm) (cartesianFaceIso_over a ha i)

/-- The underlying face comparison is the canonical chosen-pullback comparison. -/
theorem cartesianFaceIso_hom_left {Y : SimplicialObject C} (a : Y ⟶ X)
    (ha : IsCartesian a) (i : Fin 2) :
    (cartesianFaceIso a ha i).hom.left =
      (pullbackSymmetry (a.app (op ⦋0⦌)) (X.δ i) ≪≫
        (ha.isPullback (SimplexCategory.δ i)).isoPullback.symm).hom := sorry

/-- The canonical face comparison restricts to the identity along degeneracy. -/
theorem toDatumObj_degeneracy (Y : CartesianOver X) :
    degeneracyPullback X (cartesianFaceIso Y.obj.hom Y.property 1 ≪≫
      (cartesianFaceIso Y.obj.hom Y.property 0).symm) =
      𝟙 (Over.mk (Y.obj.hom.app (op ⦋0⦌))) := sorry

/-- The canonical face comparison satisfies the degree-two cocycle equation. -/
theorem toDatumObj_cocycle (Y : CartesianOver X) :
    cocycleLeft X (cartesianFaceIso Y.obj.hom Y.property 1 ≪≫
      (cartesianFaceIso Y.obj.hom Y.property 0).symm) =
    cocycleRight X (cartesianFaceIso Y.obj.hom Y.property 1 ≪≫
      (cartesianFaceIso Y.obj.hom Y.property 0).symm) := sorry

/-- Extract the degree-zero object and its canonical face comparison. -/
def toDatumObj (Y : CartesianOver X) : CartesianDatum X :=
  ofPullbackIso (Over.mk (Y.obj.hom.app (op ⦋0⦌)))
    (cartesianFaceIso Y.obj.hom Y.property 1 ≪≫
      (cartesianFaceIso Y.obj.hom Y.property 0).symm)
    (toDatumObj_degeneracy Y) (toDatumObj_cocycle Y)

/-- The extracted object over degree zero is the original degree-zero object. -/
theorem toDatumObj_schemeOver (Y : CartesianOver X) :
    (toDatumObj Y).schemeOver = Over.mk (Y.obj.hom.app (op ⦋0⦌)) := sorry

/-- The degree-zero component of an over-map commutes with the base morphisms. -/
theorem toDatumMap_over {Y Z : CartesianOver X} (f : Y ⟶ Z) :
    f.hom.left.app (op ⦋0⦌) ≫ Z.obj.hom.app (op ⦋0⦌) =
      Y.obj.hom.app (op ⦋0⦌) := sorry

/-- Extract the degree-zero over-map from a morphism of cartesian simplicial objects. -/
def toDatumMapOver {Y Z : CartesianOver X} (f : Y ⟶ Z) :
    (toDatumObj Y).schemeOver ⟶ (toDatumObj Z).schemeOver :=
  Over.homMk (f.hom.left.app (op ⦋0⦌)) (toDatumMap_over f)

/-- Degree-zero over-maps commute with the extracted face isomorphisms. -/
theorem toDatumMap_comm {Y Z : CartesianOver X} (f : Y ⟶ Z) :
    (Over.pullback (X.δ (1 : Fin 2))).map (toDatumMapOver f) ≫ (toDatumObj Z).iso.hom =
      (toDatumObj Y).iso.hom ≫
        (Over.pullback (X.δ (0 : Fin 2))).map (toDatumMapOver f) := sorry

/-- Extract a compatible descent morphism from a cartesian simplicial over-map. -/
def toDatumMap {Y Z : CartesianOver X} (f : Y ⟶ Z) : toDatumObj Y ⟶ toDatumObj Z :=
  homMk (toDatumMapOver f) (toDatumMap_comm f)

/-- Degree-zero extraction preserves identities. -/
theorem toDatum_map_id (Y : CartesianOver X) :
    toDatumMap (𝟙 Y) = 𝟙 (toDatumObj Y) := sorry

/-- Degree-zero extraction preserves composition. -/
theorem toDatum_map_comp {Y Z W : CartesianOver X} (f : Y ⟶ Z) (g : Z ⟶ W) :
    toDatumMap (f ≫ g) = toDatumMap f ≫ toDatumMap g := sorry

/-- The functor extracting descent data from cartesian simplicial objects. -/
def toDatum : CartesianOver X ⥤ CartesianDatum X where
  obj := toDatumObj
  map := toDatumMap
  map_id := toDatum_map_id
  map_comp := toDatum_map_comp

/-- Extraction has the stated object assignment. -/
theorem toDatum_obj (Y : CartesianOver X) : toDatum.obj Y = toDatumObj Y := sorry

/-- Last-vertex pullback comparisons commute with every simplex operator. -/
theorem unitAppIso_naturality (Y : CartesianOver X) {n m : SimplexCategoryᵒᵖ}
    (f : n ⟶ m) :
    Y.obj.left.map f ≫
      (Y.property.isPullback
        (SimplexCategory.const ⦋0⦌ m.unop (Fin.last m.unop.len))).isoPullback.hom =
    (Y.property.isPullback
        (SimplexCategory.const ⦋0⦌ n.unop (Fin.last n.unop.len))).isoPullback.hom ≫
      (ofDatumObj (toDatumObj Y)).map f := sorry

/-- The original cartesian object is canonically isomorphic to its last-vertex reconstruction. -/
def unitAppIso (Y : CartesianOver X) : Y.obj.left ≅ ofDatumObj (toDatumObj Y) :=
  NatIso.ofComponents (fun n ↦ (Y.property.isPullback
    (SimplexCategory.const ⦋0⦌ n.unop (Fin.last n.unop.len))).isoPullback)
    (unitAppIso_naturality Y)

/-- Each unit component is the canonical comparison of the last-vertex pullback square. -/
theorem unitAppIso_app (Y : CartesianOver X) (n : SimplexCategoryᵒᵖ) :
    (unitAppIso Y).app n = (Y.property.isPullback
      (SimplexCategory.const ⦋0⦌ n.unop (Fin.last n.unop.len))).isoPullback := sorry

/-- The canonical reconstruction comparison lies over the simplicial base. -/
theorem unitApp_over (Y : CartesianOver X) :
    (unitAppIso Y).hom ≫ ofDatumHom (toDatumObj Y) = Y.obj.hom := sorry

/-- The unit comparison lifted to the category of cartesian objects over the base. -/
def unitApp (Y : CartesianOver X) : Y ≅ ofDatum.obj (toDatum.obj Y) :=
  InducedCategory.isoMk (Over.isoMk (unitAppIso Y) (unitApp_over Y))

/-- The underlying unit over-map is the canonical reconstruction comparison. -/
theorem unitApp_hom_left (Y : CartesianOver X) :
    (unitApp Y).hom.hom.left = (unitAppIso Y).hom := sorry

/-- The unit comparisons are natural in cartesian simplicial over-maps. -/
theorem unitIso_naturality {Y Z : CartesianOver X} (f : Y ⟶ Z) :
    f ≫ (unitApp Z).hom = (unitApp Y).hom ≫ (toDatum ⋙ ofDatum).map f := sorry

/-- The natural unit isomorphism of extraction followed by reconstruction. -/
def unitIso : 𝟭 (CartesianOver X) ≅ toDatum ⋙ ofDatum :=
  NatIso.ofComponents (fun Y ↦ unitApp Y) unitIso_naturality

/-- The degree-zero comparison admits the canonical inverse pullback lift. -/
theorem counitSchemeOverIso_lift_w (D : CartesianDatum X) :
    D.schemeOver.hom ≫ vertexMap ⦋0⦌ = (𝟙 D.schemeOver.left) ≫ D.schemeOver.hom := sorry

/-- The degree-zero projection followed by its canonical lift is the identity. -/
theorem counitSchemeOverIso_hom_inv_id (D : CartesianDatum X) :
    pullback.snd (vertexMap ⦋0⦌) D.schemeOver.hom ≫
      pullback.lift D.schemeOver.hom (𝟙 _) (counitSchemeOverIso_lift_w D) =
      𝟙 (objAt D (op ⦋0⦌)) := sorry

/-- The canonical degree-zero lift followed by its projection is the identity. -/
theorem counitSchemeOverIso_inv_hom_id (D : CartesianDatum X) :
    pullback.lift D.schemeOver.hom (𝟙 _) (counitSchemeOverIso_lift_w D) ≫
      pullback.snd (vertexMap ⦋0⦌) D.schemeOver.hom = 𝟙 D.schemeOver.left := sorry

/-- The degree-zero projection lies over the identity of the degree-zero base. -/
theorem counitSchemeOverIso_over (D : CartesianDatum X) :
    pullback.snd (vertexMap ⦋0⦌) D.schemeOver.hom ≫ D.schemeOver.hom =
      (toDatumObj (ofDatumObjOver D)).schemeOver.hom := sorry

/-- The reconstructed degree-zero object is canonically isomorphic to the original over-object. -/
def counitSchemeOverIso (D : CartesianDatum X) :
    (toDatumObj (ofDatumObjOver D)).schemeOver ≅ D.schemeOver :=
  Over.isoMk
    { hom := pullback.snd (vertexMap ⦋0⦌) D.schemeOver.hom
      inv := pullback.lift D.schemeOver.hom (𝟙 _) (counitSchemeOverIso_lift_w D)
      hom_inv_id := counitSchemeOverIso_hom_inv_id D
      inv_hom_id := counitSchemeOverIso_inv_hom_id D }
    (counitSchemeOverIso_over D)

/-- The underlying counit over-map is the degree-zero pullback projection. -/
theorem counitSchemeOverIso_hom_left (D : CartesianDatum X) :
    (counitSchemeOverIso D).hom.left =
      pullback.snd (vertexMap ⦋0⦌) D.schemeOver.hom := sorry

/-- The counit projection commutes with the descent face isomorphisms. -/
theorem counitApp_hom_comm (D : CartesianDatum X) :
    (Over.pullback (X.δ (1 : Fin 2))).map (counitSchemeOverIso D).hom ≫ D.iso.hom =
      (toDatumObj (ofDatumObjOver D)).iso.hom ≫
        (Over.pullback (X.δ (0 : Fin 2))).map (counitSchemeOverIso D).hom := sorry

/-- The inverse counit lift commutes with the descent face isomorphisms. -/
theorem counitApp_inv_comm (D : CartesianDatum X) :
    (Over.pullback (X.δ (1 : Fin 2))).map (counitSchemeOverIso D).inv ≫
        (toDatumObj (ofDatumObjOver D)).iso.hom =
      D.iso.hom ≫ (Over.pullback (X.δ (0 : Fin 2))).map (counitSchemeOverIso D).inv := sorry

/-- The counit morphism followed by its inverse is the identity descent morphism. -/
theorem counitApp_hom_inv_id (D : CartesianDatum X) :
    homMk (counitSchemeOverIso D).hom (counitApp_hom_comm D) ≫
      homMk (counitSchemeOverIso D).inv (counitApp_inv_comm D) =
      𝟙 (toDatumObj (ofDatumObjOver D)) := sorry

/-- The inverse counit followed by the counit is the identity descent morphism. -/
theorem counitApp_inv_hom_id (D : CartesianDatum X) :
    homMk (counitSchemeOverIso D).inv (counitApp_inv_comm D) ≫
      homMk (counitSchemeOverIso D).hom (counitApp_hom_comm D) = 𝟙 D := sorry

/-- The counit isomorphism between reconstructed descent data and the original datum. -/
def counitApp (D : CartesianDatum X) : toDatum.obj (ofDatum.obj D) ≅ D where
  hom := homMk (counitSchemeOverIso D).hom (counitApp_hom_comm D)
  inv := homMk (counitSchemeOverIso D).inv (counitApp_inv_comm D)
  hom_inv_id := counitApp_hom_inv_id D
  inv_hom_id := counitApp_inv_hom_id D

/-- The underlying counit descent morphism is the canonical degree-zero over-map. -/
theorem counitApp_hom_left (D : CartesianDatum X) :
    (counitApp D).hom.left = (counitSchemeOverIso D).hom := sorry

/-- The counit comparisons are natural in descent morphisms. -/
theorem counitIso_naturality {D E : CartesianDatum X} (f : D ⟶ E) :
    (ofDatum ⋙ toDatum).map f ≫ (counitApp E).hom = (counitApp D).hom ≫ f := sorry

/-- The natural counit isomorphism of reconstruction followed by extraction. -/
def counitIso : ofDatum ⋙ toDatum ≅ 𝟭 (CartesianDatum X) :=
  NatIso.ofComponents (fun D ↦ counitApp D) counitIso_naturality

/-- Components of `unitIso` are `unitApp`. -/
theorem unitIso_app (Y : CartesianOver X) : unitIso.app Y = unitApp Y := sorry

/-- Components of `counitIso` are `counitApp`. -/
theorem counitIso_app (D : CartesianDatum X) : counitIso.app D = counitApp D := sorry

/-- The identity of cartesian pairs is the identity over `X _⦋0⦌`. -/
theorem Hom.id_left (D : CartesianDatum X) : (Hom.id D).left = 𝟙 D.schemeOver := sorry

/-- Composition of cartesian pairs is composition over `X _⦋0⦌`. -/
theorem Hom.comp_left {D E F : CartesianDatum X} (f : Hom D E) (g : Hom E F) :
    (Hom.comp f g).left = f.left ≫ g.left := sorry

/-- The structure morphism of `ofDatumObjOver D` is `ofDatumHom D`. -/
theorem ofDatumObjOver_hom (D : CartesianDatum X) :
    (ofDatumObjOver D).obj.hom = ofDatumHom D := sorry

end CartesianDatum

/-- Cartesian simplicial objects over a base are equivalent to its degree-zero descent data. -/
def cartesianOverEquivalence (X : SimplicialObject C) : CartesianOver X ≌ CartesianDatum X :=
  CategoryTheory.Equivalence.mk CartesianDatum.toDatum CartesianDatum.ofDatum
    CartesianDatum.unitIso CartesianDatum.counitIso

/-- The equivalence extracts the canonical degree-zero descent data. -/
theorem cartesianOverEquivalence_functor (X : SimplicialObject C) :
    (cartesianOverEquivalence X).functor = CartesianDatum.toDatum := sorry

/-- The inverse equivalence reconstructs last-vertex pullbacks and their simplex operators. -/
theorem cartesianOverEquivalence_inverse (X : SimplicialObject C) :
    (cartesianOverEquivalence X).inverse = CartesianDatum.ofDatum := sorry

/-- The equivalence extracts the original degree-zero object over the degree-zero base. -/
theorem cartesianOverEquivalence_functor_obj_schemeOver {X : SimplicialObject C}
    (Y : CartesianOver X) :
    ((cartesianOverEquivalence X).functor.obj Y).schemeOver =
      Over.mk (Y.obj.hom.app (op ⦋0⦌)) := sorry

end CategoryTheory.SimplicialObject
