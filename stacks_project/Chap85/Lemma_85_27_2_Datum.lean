/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Equivalence
public import stacks_project.Chap85.Lemma_85_27_2_CartesianOver

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

/-- Reidentify `Over.pullback` along an equality of base morphisms. -/
def recodePullback {A B : C} {f g : A ⟶ B} (h : f = g) :
    Over.pullback f ≅ Over.pullback g :=
  CategoryTheory.eqToIso (congrArg (fun t ↦ Over.pullback t) h)

/-- The reidentification `recodePullback h` is the identity when `h` is `rfl`. -/
theorem recodePullback_refl {A B : C} (f : A ⟶ B) :
    recodePullback (rfl : f = f) = Iso.refl (Over.pullback f) := sorry

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

/-- `degeneracyPullback` is the identity on `V` precisely when `(X.σ 0)*φ = 𝟙 V`. -/
theorem degeneracyPullback_spec {V : Over (X _⦋0⦌)}
    (φ : (Over.pullback (X.δ (1 : Fin 2))).obj V ≅
      (Over.pullback (X.δ (0 : Fin 2))).obj V) :
    degeneracyPullback X φ = 𝟙 V ↔
      (Over.pullbackId : Over.pullback (𝟙 (X _⦋0⦌)) ≅ 𝟭 _).hom.app V ≫
          degeneracyPullback X φ ≫
            (Over.pullbackId : Over.pullback (𝟙 (X _⦋0⦌)) ≅ 𝟭 _).inv.app V =
        𝟙 _ := sorry

/-- The pullback of `φ` along a 2-face `X.δ i`, as a morphism over `X _⦋2⦌`. -/
def facePullback (i : Fin 3) {V : Over (X _⦋0⦌)}
    (φ : (Over.pullback (X.δ (1 : Fin 2))).obj V ≅
      (Over.pullback (X.δ (0 : Fin 2))).obj V) :
    (Over.pullback (X.δ i ≫ X.δ (1 : Fin 2))).obj V ⟶
      (Over.pullback (X.δ i ≫ X.δ (0 : Fin 2))).obj V :=
  (Over.pullbackComp (X.δ i) (X.δ (1 : Fin 2))).hom.app V ≫
    (Over.pullback (X.δ i)).map φ.hom ≫
    (Over.pullbackComp (X.δ i) (X.δ (0 : Fin 2))).inv.app V

/-- `facePullback i φ` is `Over.pullback (X.δ i)` applied to `φ`, transported by `pullbackComp`. -/
theorem facePullback_eq (i : Fin 3) {V : Over (X _⦋0⦌)}
    (φ : (Over.pullback (X.δ (1 : Fin 2))).obj V ≅
      (Over.pullback (X.δ (0 : Fin 2))).obj V) :
    facePullback X i φ =
      (Over.pullbackComp (X.δ i) (X.δ (1 : Fin 2))).hom.app V ≫
        (Over.pullback (X.δ i)).map φ.hom ≫
        (Over.pullbackComp (X.δ i) (X.δ (0 : Fin 2))).inv.app V := sorry

/-- The source of the `X _⦋2⦌` cocycle, namely the pullback of `V` along `X.δ 2 ≫ X.δ 1`. -/
abbrev cocycleSource (V : Over (X _⦋0⦌)) : Over (X _⦋2⦌) :=
  (Over.pullback (X.δ (2 : Fin 3) ≫ X.δ (1 : Fin 2))).obj V

/-- `cocycleSource V` is the pullback of `V` along `X.δ 2 ≫ X.δ 1`. -/
theorem cocycleSource_eq (V : Over (X _⦋0⦌)) :
    cocycleSource X V = (Over.pullback (X.δ (2 : Fin 3) ≫ X.δ (1 : Fin 2))).obj V := sorry

/-- The target of the `X _⦋2⦌` cocycle, namely the pullback of `V` along `X.δ 1 ≫ X.δ 0`. -/
abbrev cocycleTarget (V : Over (X _⦋0⦌)) : Over (X _⦋2⦌) :=
  (Over.pullback (X.δ (1 : Fin 3) ≫ X.δ (0 : Fin 2))).obj V

/-- `cocycleTarget V` is the pullback of `V` along `X.δ 1 ≫ X.δ 0`. -/
theorem cocycleTarget_eq (V : Over (X _⦋0⦌)) :
    cocycleTarget X V = (Over.pullback (X.δ (1 : Fin 3) ≫ X.δ (0 : Fin 2))).obj V := sorry

/-- `(X.δ 1)*φ` transported to a morphism `cocycleSource V ⟶ cocycleTarget V`. -/
def cocycleLeft {V : Over (X _⦋0⦌)}
    (φ : (Over.pullback (X.δ (1 : Fin 2))).obj V ≅
      (Over.pullback (X.δ (0 : Fin 2))).obj V) :
    cocycleSource X V ⟶ cocycleTarget X V :=
  (recodePullback (X.δ_comp_δ_self (i := (1 : Fin 2))).symm).hom.app V ≫
    facePullback X 1 φ

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

/-- `cocycleLeft` and `cocycleRight` are the two sides of the displayed `X _⦋2⦌` cocycle. -/
theorem cocycleLeft_eq_facePullback {V : Over (X _⦋0⦌)}
    (φ : (Over.pullback (X.δ (1 : Fin 2))).obj V ≅
      (Over.pullback (X.δ (0 : Fin 2))).obj V) :
    cocycleLeft X φ =
      (recodePullback (X.δ_comp_δ_self (i := (1 : Fin 2))).symm).hom.app V ≫
        facePullback X 1 φ := sorry

/-- `cocycleRight` is `(X.δ 0)*φ ∘ (X.δ 2)*φ` after the `δ_comp_δ` identifications. -/
theorem cocycleRight_eq_facePullback {V : Over (X _⦋0⦌)}
    (φ : (Over.pullback (X.δ (1 : Fin 2))).obj V ≅
      (Over.pullback (X.δ (0 : Fin 2))).obj V) :
    cocycleRight X φ =
      facePullback X 2 φ ≫
        (recodePullback
          (X.δ_comp_δ (i := (0 : Fin 2)) (j := (1 : Fin 2)) (Fin.zero_le _))).hom.app V ≫
        facePullback X 0 φ ≫
        (recodePullback
          (X.δ_comp_δ (i := (0 : Fin 2)) (j := (0 : Fin 2)) le_rfl).symm).hom.app V := sorry

/-- A pair `(V, φ)` with degeneracy identity and `X _⦋2⦌` cocycle. -/
structure CartesianDatum where
  /-- The object `V` over `X _⦋0⦌`. -/
  schemeOver : Over (X _⦋0⦌)
  /-- The isomorphism `φ` over `X _⦋1⦌` between the two face pullbacks of `V`. -/
  iso :
    (Over.pullback (X.δ (1 : Fin 2))).obj schemeOver ≅
      (Over.pullback (X.δ (0 : Fin 2))).obj schemeOver
  /-- The degeneracy identity `(X.σ 0)*φ = 𝟙 V`. -/
  degeneracy : degeneracyPullback X iso = 𝟙 schemeOver
  /-- The cocycle `(X.δ 1)*φ = (X.δ 0)*φ ∘ (X.δ 2)*φ` over `X _⦋2⦌`. -/
  cocycle : cocycleLeft X iso = cocycleRight X iso

namespace CartesianDatum

variable {X}

/-- Build cartesian data from an object over `X _⦋0⦌`, an isomorphism over `X _⦋1⦌`, and
the degeneracy and cocycle proofs. -/
def ofPullbackIso (V : Over (X _⦋0⦌))
    (e : (Over.pullback (X.δ (1 : Fin 2))).obj V ≅
      (Over.pullback (X.δ (0 : Fin 2))).obj V)
    (hdeg : degeneracyPullback X e = 𝟙 V)
    (hcyc : cocycleLeft X e = cocycleRight X e) : CartesianDatum X where
  schemeOver := V
  iso := e
  degeneracy := hdeg
  cocycle := hcyc

/-- The defining degeneracy and cocycle laws of a cartesian pair. -/
theorem spec (D : CartesianDatum X) :
    degeneracyPullback X D.iso = 𝟙 D.schemeOver ∧
      cocycleLeft X D.iso = cocycleRight X D.iso := sorry

/-- A morphism of cartesian pairs is a map of the underlying objects over `X _⦋0⦌` commuting
with `φ`. -/
structure Hom (D E : CartesianDatum X) where
  /-- The underlying morphism over `X _⦋0⦌`. -/
  left : D.schemeOver ⟶ E.schemeOver
  /-- Commutation with the face-pullback isomorphisms over `X _⦋1⦌`. -/
  comm :
    (Over.pullback (X.δ (1 : Fin 2))).map left ≫ E.iso.hom =
      D.iso.hom ≫ (Over.pullback (X.δ (0 : Fin 2))).map left

/-- Build a morphism of cartesian pairs from an over-map commuting with `φ`. -/
def homMk {D E : CartesianDatum X} (left : D.schemeOver ⟶ E.schemeOver)
    (comm :
      (Over.pullback (X.δ (1 : Fin 2))).map left ≫ E.iso.hom =
        D.iso.hom ≫ (Over.pullback (X.δ (0 : Fin 2))).map left) :
    Hom D E :=
  ⟨left, comm⟩

/-- The identity morphism of cartesian pairs. -/
def Hom.id (D : CartesianDatum X) : Hom D D :=
  homMk (𝟙 D.schemeOver) sorry

/-- Composition of morphisms of cartesian pairs. -/
def Hom.comp {D E F : CartesianDatum X} (f : Hom D E) (g : Hom E F) : Hom D F :=
  homMk (f.left ≫ g.left) sorry

/-- The left component of `homMk left comm` is `left`. -/
theorem homMk_left {D E : CartesianDatum X} (left : D.schemeOver ⟶ E.schemeOver)
    (comm :
      (Over.pullback (X.δ (1 : Fin 2))).map left ≫ E.iso.hom =
        D.iso.hom ≫ (Over.pullback (X.δ (0 : Fin 2))).map left) :
    (homMk left comm).left = left := sorry

/-- The category of pairs `(V, φ)` over `X`. -/
instance category : Category.{v} (CartesianDatum X) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- The last-vertex operator `X(τ^n_n) : X.obj (op n) ⟶ X _⦋0⦌`. -/
def vertexMap (n : SimplexCategory) : X.obj (op n) ⟶ X _⦋0⦌ :=
  X.map (SimplexCategory.const ⦋0⦌ n (Fin.last n.len)).op

/-- `vertexMap n` is `X.map` of `const ⦋0⦌ n (Fin.last n.len)`. -/
theorem vertexMap_eq (n : SimplexCategory) :
    vertexMap n = X.map (SimplexCategory.const ⦋0⦌ n (Fin.last n.len)).op := sorry

/-- The edge operator `X(τ^m_{β(n)m}) : X.obj (op m) ⟶ X _⦋1⦌`. -/
def edgeMap {n m : SimplexCategory} (β : n ⟶ m) : X.obj (op m) ⟶ X _⦋1⦌ :=
  X.map (SimplexCategory.mkOfLe (β.toOrderHom (Fin.last n.len)) (Fin.last m.len)
      (Fin.le_last _)).op

/-- `edgeMap β` is `X.map` of `mkOfLe (β (last)) last`. -/
theorem edgeMap_eq {n m : SimplexCategory} (β : n ⟶ m) :
    edgeMap β =
      X.map (SimplexCategory.mkOfLe (β.toOrderHom (Fin.last n.len)) (Fin.last m.len)
        (Fin.le_last _)).op := sorry

/-- The reconstructed degree-`n` object `X_n ×_{X(τ^n_n)} V`. -/
abbrev objAt (D : CartesianDatum X) (n : SimplexCategoryᵒᵖ) : C :=
  pullback (vertexMap n.unop) D.schemeOver.hom

/-- `objAt D n` is the chosen pullback of `vertexMap n.unop` along `D.schemeOver.hom`. -/
theorem objAt_eq (D : CartesianDatum X) (n : SimplexCategoryᵒᵖ) :
    objAt D n = pullback (vertexMap n.unop) D.schemeOver.hom := sorry

/-- Commutativity witness for the map from `objAt D (op m)` into the `δ 1` face pullback. -/
theorem toFace_w (D : CartesianDatum X) {n m : SimplexCategory} (β : n ⟶ m) :
    pullback.snd (vertexMap m) D.schemeOver.hom ≫ D.schemeOver.hom =
      (pullback.fst (vertexMap m) D.schemeOver.hom ≫ edgeMap β) ≫
        X.δ (1 : Fin 2) := sorry

/-- The comparison `Y_m ⟶ V ×_{X_0, X.δ 1} X_1` used to apply `φ`. -/
def toFace (D : CartesianDatum X) {n m : SimplexCategory} (β : n ⟶ m) :
    objAt D (op m) ⟶ ((Over.pullback (X.δ (1 : Fin 2))).obj D.schemeOver).left :=
  pullback.lift (pullback.snd _ _) (pullback.fst _ _ ≫ edgeMap β) (toFace_w D β)

/-- `toFace` projects to `V` by `pullback.snd`. -/
theorem toFace_fst (D : CartesianDatum X) {n m : SimplexCategory} (β : n ⟶ m) :
    toFace D β ≫ pullback.fst D.schemeOver.hom (X.δ (1 : Fin 2)) =
      pullback.snd (vertexMap m) D.schemeOver.hom := sorry

/-- Commutativity witness for the reconstructed simplicial operator `Y(β)`. -/
theorem mapSimplex_w (D : CartesianDatum X) {n m : SimplexCategory} (β : n ⟶ m) :
    (pullback.fst (vertexMap m) D.schemeOver.hom ≫ X.map β.op) ≫
        vertexMap n =
      (toFace D β ≫ D.iso.hom.left ≫ pullback.fst D.schemeOver.hom (X.δ (0 : Fin 2))) ≫
        D.schemeOver.hom := sorry

/-- The reconstructed operator `Y(β) : Y_m ⟶ Y_n`, as the pullback of `φ` along
`X(τ^m_{β(n)m})` followed by projection to `Y_n`. -/
def mapSimplex (D : CartesianDatum X) {n m : SimplexCategory} (β : n ⟶ m) :
    objAt D (op m) ⟶ objAt D (op n) :=
  pullback.lift (pullback.fst _ _ ≫ X.map β.op)
    (toFace D β ≫ D.iso.hom.left ≫ pullback.fst _ _) (mapSimplex_w D β)

/-- `mapSimplex` projects to `X_n` by `X.map β.op`. -/
theorem mapSimplex_fst (D : CartesianDatum X) {n m : SimplexCategory} (β : n ⟶ m) :
    mapSimplex D β ≫ pullback.fst (vertexMap n) D.schemeOver.hom =
      pullback.fst (vertexMap m) D.schemeOver.hom ≫ X.map β.op := sorry

/-- The reconstructed simplicial object with `Y_n = X_n ×_{X(τ^n_n)} V`. -/
def ofDatumObj (D : CartesianDatum X) : SimplicialObject C where
  obj n := objAt D n
  map f := mapSimplex D f.unop
  map_id := fun _ ↦ sorry
  map_comp := fun _ _ ↦ sorry

/-- Degree `n` of `ofDatumObj D` is the chosen pullback along `vertexMap n`. -/
theorem ofDatumObj_obj (D : CartesianDatum X) (n : SimplexCategoryᵒᵖ) :
    (ofDatumObj D).obj n = objAt D n := sorry

/-- The structure morphism `Y ⟶ X` with components `pullback.fst`. -/
def ofDatumHom (D : CartesianDatum X) : ofDatumObj D ⟶ X where
  app n := pullback.fst (vertexMap n.unop) D.schemeOver.hom
  naturality := sorry

/-- Components of `ofDatumHom D` are the projections `Y_n ⟶ X_n`. -/
theorem ofDatumHom_app (D : CartesianDatum X) (n : SimplexCategoryᵒᵖ) :
    (ofDatumHom D).app n = pullback.fst (vertexMap n.unop) D.schemeOver.hom := sorry

/-- The reconstructed object cartesian over `X`. -/
def ofDatumObjOver (D : CartesianDatum X) : CartesianOver X :=
  CartesianOver.ofHom (ofDatumHom D) sorry

/-- Inverse reconstruction as a functor. -/
def ofDatum : CartesianDatum X ⥤ CartesianOver X where
  obj D := ofDatumObjOver D
  map {D E} f :=
    InducedCategory.homMk <|
      Over.homMk
        { app := fun n ↦
            pullback.lift (pullback.fst _ _)
              (pullback.snd _ _ ≫ f.left.left) sorry
          naturality := sorry }
        sorry
  map_id := fun _ ↦ sorry
  map_comp := fun _ _ ↦ sorry

/-- The inverse functor sends a pair to `ofDatumObjOver`. -/
theorem ofDatum_obj (D : CartesianDatum X) :
    ofDatum.obj D = ofDatumObjOver D := sorry

/-- The face-square comparison of a cartesian morphism, as an isomorphism over `X _⦋1⦌`. -/
def cartesianFaceIso {Y : SimplicialObject C} (a : Y ⟶ X) (ha : IsCartesian a) (i : Fin 2) :
    (Over.pullback (X.δ i)).obj (Over.mk (a.app (op ⦋0⦌))) ≅ Over.mk (a.app (op ⦋1⦌)) :=
  Over.isoMk
    (pullbackSymmetry (a.app (op ⦋0⦌)) (X.δ i) ≪≫
      (ha.isPullback (SimplexCategory.δ i)).isoPullback.symm)
    sorry

/-- The underlying left morphism of `cartesianFaceIso` is the pullback comparison. -/
theorem cartesianFaceIso_hom_left {Y : SimplicialObject C} (a : Y ⟶ X)
    (ha : IsCartesian a) (i : Fin 2) :
    (cartesianFaceIso a ha i).hom.left =
      (pullbackSymmetry (a.app (op ⦋0⦌)) (X.δ i) ≪≫
        (ha.isPullback (SimplexCategory.δ i)).isoPullback.symm).hom := sorry

/-- Extract `(Y _⦋0⦌, φ)` from a cartesian structure morphism. -/
def toDatumObj (Y : CartesianOver X) : CartesianDatum X :=
  ofPullbackIso (Over.mk (Y.obj.hom.app (op ⦋0⦌)))
    (cartesianFaceIso Y.obj.hom Y.property 1 ≪≫
      (cartesianFaceIso Y.obj.hom Y.property 0).symm)
    sorry sorry

/-- The object over `X _⦋0⦌` extracted by `toDatumObj` is `Y _⦋0⦌`. -/
theorem toDatumObj_schemeOver (Y : CartesianOver X) :
    (toDatumObj Y).schemeOver = Over.mk (Y.obj.hom.app (op ⦋0⦌)) := sorry

/-- Forward extraction as a functor. -/
def toDatum : CartesianOver X ⥤ CartesianDatum X where
  obj Y := toDatumObj Y
  map {Y Z} f :=
    homMk (Over.homMk (f.hom.left.app (op ⦋0⦌)) sorry) sorry
  map_id := fun _ ↦ sorry
  map_comp := fun _ _ ↦ sorry

/-- The forward functor sends `Y` to `toDatumObj Y`. -/
theorem toDatum_obj (Y : CartesianOver X) : toDatum.obj Y = toDatumObj Y := sorry

/-- The cartesian comparison `Y_n ≅ X_n ×_{X_0} Y_0`. -/
def unitAppIso (Y : CartesianOver X) : Y.obj.left ≅ ofDatumObj (toDatumObj Y) :=
  NatIso.ofComponents
    (fun n ↦
      (Y.property.isPullback
        (SimplexCategory.const ⦋0⦌ n.unop (Fin.last n.unop.len))).isoPullback)
    sorry

/-- Components of `unitAppIso` are the chosen-pullback comparisons of the last-vertex squares. -/
theorem unitAppIso_app (Y : CartesianOver X) (n : SimplexCategoryᵒᵖ) :
    (unitAppIso Y).app n =
      (Y.property.isPullback
        (SimplexCategory.const ⦋0⦌ n.unop (Fin.last n.unop.len))).isoPullback := sorry

/-- The unit isomorphism of the cartesian-over equivalence, at an object `Y`. -/
def unitApp (Y : CartesianOver X) : Y ≅ ofDatum.obj (toDatum.obj Y) :=
  InducedCategory.isoMk <| Over.isoMk (unitAppIso Y) sorry

/-- The left morphism of `unitApp Y` is `unitAppIso Y`. -/
theorem unitApp_hom_left (Y : CartesianOver X) :
    (unitApp Y).hom.hom.left = (unitAppIso Y).hom := sorry

/-- The unit natural isomorphism `𝟭 (CartesianOver X) ≅ toDatum ⋙ ofDatum`. -/
def unitIso : 𝟭 (CartesianOver X) ≅ toDatum ⋙ ofDatum :=
  NatIso.ofComponents (fun Y ↦ unitApp Y) sorry

/-- Degree-zero comparison `Y_0 ≅ V` for reconstructed data. -/
def counitSchemeOverIso (D : CartesianDatum X) :
    (toDatumObj (ofDatumObjOver D)).schemeOver ≅ D.schemeOver :=
  Over.isoMk
    { hom := pullback.snd (vertexMap ⦋0⦌) D.schemeOver.hom
      inv := pullback.lift D.schemeOver.hom (𝟙 _) sorry
      hom_inv_id := sorry
      inv_hom_id := sorry }
    sorry

/-- The underlying left morphism of `counitSchemeOverIso` is `pullback.snd`. -/
theorem counitSchemeOverIso_hom_left (D : CartesianDatum X) :
    (counitSchemeOverIso D).hom.left =
      pullback.snd (vertexMap ⦋0⦌) D.schemeOver.hom := sorry

/-- The counit isomorphism of the cartesian-over equivalence, at a pair `D`. -/
def counitApp (D : CartesianDatum X) : toDatum.obj (ofDatum.obj D) ≅ D :=
  { hom := homMk (counitSchemeOverIso D).hom sorry
    inv := homMk (counitSchemeOverIso D).inv sorry
    hom_inv_id := sorry
    inv_hom_id := sorry }

/-- The left component of `counitApp D` is `counitSchemeOverIso D`. -/
theorem counitApp_hom_left (D : CartesianDatum X) :
    (counitApp D).hom.left = (counitSchemeOverIso D).hom := sorry

/-- The counit natural isomorphism `ofDatum ⋙ toDatum ≅ 𝟭 (CartesianDatum X)`. -/
def counitIso : ofDatum ⋙ toDatum ≅ 𝟭 (CartesianDatum X) :=
  NatIso.ofComponents (fun D ↦ counitApp D) sorry

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

end CategoryTheory.SimplicialObject
