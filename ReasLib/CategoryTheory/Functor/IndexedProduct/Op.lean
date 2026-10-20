/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.IndexedProduct.Basic

/-!
# Opposite-oriented indexed products

Given a presheaf of indices `U : Dᵒᵖ ⥤ Type w` and a covariant valued functor
`V : D ⥤ C`, this leaf constructs `Functor.indexedProd.op U V`.  It owns the opposite
orientation's object and structure-map formulas, functoriality in both variables, and the
curried bifunctor.  It is independent of the standard-orientation construction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe i w d v u j e

namespace CategoryTheory.Functor

variable {D : Type i} [Category.{d} D] {C : Type u} [Category.{v} C]

variable (U : Dᵒᵖ ⥤ Type w) (V : D ⥤ C)
variable [HasIndexedProd.Op U V]

/- The following map owner is the covariant counterpart of `indexedProd.mapHom`. -/
/-- The degreewise reindexing morphism underlying the opposite-oriented indexed product. -/
@[stacks 0B15 "opposite indexed-product reindexing morphism"]
def indexedProd.op.mapHom {d₁ d₂ : D} (f : d₁ ⟶ d₂) :
    (∏ᶜ fun _ : U.obj (Opposite.op d₁) ↦ V.obj d₁) ⟶
      (∏ᶜ fun _ : U.obj (Opposite.op d₂) ↦ V.obj d₂) :=
  Pi.map' (U.map f.op) (fun _ ↦ V.map f)

/-- Opposite-oriented indexed-product reindexing preserves identity morphisms. -/
theorem indexedProd.op.mapHom.id (d : D) :
    indexedProd.op.mapHom U V (𝟙 d) =
      𝟙 (∏ᶜ fun _ : U.obj (Opposite.op d) ↦ V.obj d) := sorry

/-- Opposite-oriented indexed-product reindexing preserves composition. -/
theorem indexedProd.op.mapHom.comp {d₁ d₂ d₃ : D}
    (f : d₁ ⟶ d₂) (g : d₂ ⟶ d₃) :
    indexedProd.op.mapHom U V (f ≫ g) =
      indexedProd.op.mapHom U V f ≫ indexedProd.op.mapHom U V g := sorry

/- The following owner keeps the same construction available when the valued functor is
covariant.  This is the orientation used by cosimplicial cotensors. -/
/-- The opposite-oriented indexed product copresheaf, with value at `d` the product of
`U.obj (Opposite.op d)` copies of `V.obj d`. -/
@[stacks 0B15 "covariant indexed product"]
def indexedProd.op : D ⥤ C where
  obj d := ∏ᶜ (fun _ : U.obj (Opposite.op d) ↦ V.obj d)
  map f := indexedProd.op.mapHom U V f
  map_id d := indexedProd.op.mapHom.id U V d
  map_comp f g := indexedProd.op.mapHom.comp U V f g

/-- The structure map of an opposite-oriented indexed product commutes with each projection. -/
@[stacks 0B15 "opposite indexed-product projection square"]
theorem indexedProd.op.map.π {d₁ d₂ : D} (f : d₁ ⟶ d₂)
    (u : U.obj (Opposite.op d₂)) :
    CommSq
      ((indexedProd.op U V).map f)
      (Pi.π (fun _ : U.obj (Opposite.op d₁) ↦ V.obj d₁) (U.map f.op u))
      (Pi.π (fun _ : U.obj (Opposite.op d₂) ↦ V.obj d₂) u)
      (V.map f) := sorry

/-- A morphism into an opposite-oriented indexed product is componentwise natural after
evaluation at every index. -/
@[stacks 0B15 "opposite indexed-product morphism naturality"]
theorem indexedProd.op.hom_naturality {X : D ⥤ C}
    (h : X ⟶ indexedProd.op U V) {d₁ d₂ : D} (f : d₁ ⟶ d₂)
    (u : U.obj (Opposite.op d₂)) :
    CommSq
      (X.map f)
      (h.app d₁ ≫
        Pi.π (fun _ : U.obj (Opposite.op d₁) ↦ V.obj d₁) (U.map f.op u))
      (h.app d₂ ≫ Pi.π (fun _ : U.obj (Opposite.op d₂) ↦ V.obj d₂) u)
      (V.map f) := sorry

/-- Morphisms into an opposite-oriented indexed product are equal when all degreewise
projections agree. -/
@[ext, stacks 0B15 "opposite indexed-product morphism extensionality"]
theorem indexedProd.op.hom_ext {X : D ⥤ C} {f g : X ⟶ indexedProd.op U V}
    (h : ∀ (d : D) (u : U.obj (Opposite.op d)),
      f.app d ≫ Pi.π (fun _ : U.obj (Opposite.op d) ↦ V.obj d) u =
        g.app d ≫ Pi.π (fun _ : U.obj (Opposite.op d) ↦ V.obj d) u) :
    f = g := sorry

/-- The value of an opposite-oriented indexed product is the corresponding target product. -/
@[simp, stacks 0B15 "opposite indexed-product object formula"]
theorem indexedProd.op.obj (d : D) :
    (indexedProd.op U V).obj d =
      ∏ᶜ (fun _ : U.obj (Opposite.op d) ↦ V.obj d) := sorry

/-- The opposite-oriented structure map reindexes factors and applies the valued functor. -/
@[simp, stacks 0B15 "opposite indexed-product map formula"]
theorem indexedProd.op.map {d₁ d₂ : D} (f : d₁ ⟶ d₂) :
    (indexedProd.op U V).map f = Pi.map' (U.map f.op) (fun _ ↦ V.map f) := sorry

/-- The covariant orientation has the same readable constant-family instance as the presheaf
orientation. -/
@[stacks 0B15 "constant-family covariant indexed product instance"]
instance indexedProd.op.hasProduct_const (U : Dᵒᵖ ⥤ Type w) (X : C) (d : D)
    [h : HasIndexedProd.Op U ((Functor.const D).obj X)] :
    HasProduct (fun _ : U.obj (Opposite.op d) ↦ X) :=
  HasIndexedProd.Op.hasProduct (U := U) (V := (Functor.const D).obj X) d

namespace indexedProd.op

section ObjectVariable

variable (U : Dᵒᵖ ⥤ Type w) {V W : D ⥤ C}

/-- The raw component used to assemble the opposite-oriented indexed-product morphism induced by
a morphism in the valued copresheaf variable. -/
@[stacks 0B15 "opposite indexed-product induced component"]
def homApp [HasIndexedProd.Op U V] [HasIndexedProd.Op U W]
    (f : V ⟶ W) (d : D) :
    (indexedProd.op U V).obj d ⟶ (indexedProd.op U W).obj d :=
  Limits.Pi.map (fun _ : U.obj (Opposite.op d) ↦ f.app d)

/-- The raw opposite-oriented indexed-product components `homApp U f` form a natural family. -/
@[stacks 0B15 "opposite indexed-product induced naturality"]
theorem homApp.naturality [HasIndexedProd.Op U V] [HasIndexedProd.Op U W]
    (f : V ⟶ W) {d₁ d₂ : D} (g : d₁ ⟶ d₂) :
    (indexedProd.op U V).map g ≫ homApp U f d₂ =
      homApp U f d₁ ≫ (indexedProd.op U W).map g := sorry

/-- A morphism of valued copresheaves induces a morphism between their opposite-oriented
indexed products. -/
@[stacks 0B15 "opposite indexed-product induced morphism"]
def hom [HasIndexedProd.Op U V] [HasIndexedProd.Op U W]
    (f : V ⟶ W) : indexedProd.op U V ⟶ indexedProd.op U W where
  app := homApp U f
  naturality := fun _ _ g ↦ homApp.naturality U f g

/-- The component of the bundled morphism induced between opposite-oriented indexed products. -/
@[simp, stacks 0B15 "opposite indexed-product induced component formula"]
theorem hom_app [HasIndexedProd.Op U V] [HasIndexedProd.Op U W]
    (f : V ⟶ W) (d : D) :
    (hom U f).app d = homApp U f d := sorry

/-- Evaluation of an induced opposite-oriented indexed-product morphism at a product factor. -/
@[reassoc (attr := simp), stacks 0B15 "opposite indexed-product induced projection formula"]
theorem hom.π
    [HasIndexedProd.Op U V] [HasIndexedProd.Op U W]
    (f : V ⟶ W) (d : D) (u : U.obj (Opposite.op d)) :
    (hom U f).app d ≫ Pi.π (fun _ : U.obj (Opposite.op d) ↦ W.obj d) u =
      Pi.π (fun _ : U.obj (Opposite.op d) ↦ V.obj d) u ≫ f.app d := sorry

/-- Opposite-oriented indexed products preserve identity morphisms in the valued variable. -/
@[simp, stacks 0B15 "opposite indexed-product induced identity"]
theorem hom.id (V : D ⥤ C) [HasIndexedProd.Op U V] :
    hom U (𝟙 V) = 𝟙 (indexedProd.op U V) := sorry

/-- Opposite-oriented indexed products preserve composition in the valued variable. -/
@[stacks 0B15 "opposite indexed-product induced composition"]
theorem hom.comp {V W X : D ⥤ C}
    [HasIndexedProd.Op U V] [HasIndexedProd.Op U W] [HasIndexedProd.Op U X]
    (f : V ⟶ W) (g : W ⟶ X) :
    hom U (f ≫ g) = hom U f ≫ hom U g := sorry

end ObjectVariable

section IndexVariable

variable {U W : Dᵒᵖ ⥤ Type w} (V : D ⥤ C)

/-- The raw component induced contravariantly on opposite-oriented indexed products by an index
morphism. -/
@[stacks 0B15 "opposite indexed-product index-map component"]
def indexHomApp [HasIndexedProd.Op U V] [HasIndexedProd.Op W V]
    (a : U ⟶ W) (d : D) :
    (indexedProd.op W V).obj d ⟶ (indexedProd.op U V).obj d :=
  Pi.lift (fun u : U.obj (Opposite.op d) ↦
    Pi.π (fun _ : W.obj (Opposite.op d) ↦ V.obj d) (a.app (Opposite.op d) u))

/-- Opposite-oriented index-map components form a natural family. -/
@[stacks 0B15 "opposite indexed-product index-map naturality"]
theorem indexHomApp.naturality [HasIndexedProd.Op U V] [HasIndexedProd.Op W V]
    (a : U ⟶ W) {d₁ d₂ : D} (f : d₁ ⟶ d₂) :
    (indexedProd.op W V).map f ≫ indexHomApp V a d₂ =
      indexHomApp V a d₁ ≫ (indexedProd.op U V).map f := sorry

/-- A morphism of presheaves of indices induces an opposite-oriented indexed-product morphism in
the reverse direction. -/
@[stacks 0B15 "opposite indexed-product morphism in the indexing variable"]
def indexHom [HasIndexedProd.Op U V] [HasIndexedProd.Op W V]
    (a : U ⟶ W) : indexedProd.op W V ⟶ indexedProd.op U V where
  app := indexHomApp V a
  naturality := fun _ _ f ↦ indexHomApp.naturality V a f

/-- The component of an opposite-oriented index morphism is its raw component. -/
@[simp, stacks 0B15 "opposite indexed-product index-map component formula"]
theorem indexHom_app [HasIndexedProd.Op U V] [HasIndexedProd.Op W V]
    (a : U ⟶ W) (d : D) :
    (indexHom V a).app d = indexHomApp V a d := sorry

/-- An opposite-oriented indexed-product index morphism reindexes every projection. -/
@[reassoc (attr := simp), stacks 0B15 "opposite indexed-product index-map projection formula"]
theorem indexHom.π [HasIndexedProd.Op U V] [HasIndexedProd.Op W V]
    (a : U ⟶ W) (d : D) (u : U.obj (Opposite.op d)) :
    (indexHom V a).app d ≫
        Pi.π (fun _ : U.obj (Opposite.op d) ↦ V.obj d) u =
      Pi.π (fun _ : W.obj (Opposite.op d) ↦ V.obj d) (a.app (Opposite.op d) u) := sorry

/-- Opposite-oriented indexed-product reindexing preserves identity index morphisms. -/
@[simp, stacks 0B15 "opposite indexed-product index-map identity"]
theorem indexHom.id (U : Dᵒᵖ ⥤ Type w) [HasIndexedProd.Op U V] :
    indexHom V (𝟙 U) = 𝟙 (indexedProd.op U V) := sorry

/-- Opposite-oriented indexed-product reindexing reverses composition in the indexing variable. -/
@[stacks 0B15 "opposite indexed-product index-map composition"]
theorem indexHom.comp {U W X : Dᵒᵖ ⥤ Type w}
    [HasIndexedProd.Op U V] [HasIndexedProd.Op W V] [HasIndexedProd.Op X V]
    (a : U ⟶ W) (b : W ⟶ X) :
    indexHom V (a ≫ b) = indexHom V b ≫ indexHom V a := sorry

end IndexVariable

section MixedVariable

variable {U W : Dᵒᵖ ⥤ Type w} {V Z : D ⥤ C}

/-- Contravariant reindexing of opposite-oriented indexed products commutes with functoriality in
the valued copresheaf. -/
@[stacks 0B15 "opposite indexed-product variable interchange"]
theorem indexHom.naturality
    [HasIndexedProd.Op U V] [HasIndexedProd.Op U Z]
    [HasIndexedProd.Op W V] [HasIndexedProd.Op W Z]
    (a : U ⟶ W) (f : V ⟶ Z) :
    hom W f ≫ indexHom Z a = indexHom V a ≫ hom U f := sorry

end MixedVariable

section ObjectVariableFunctor

variable (U : Dᵒᵖ ⥤ Type w) [HasIndexedProds.Op U C]

/-- Opposite-oriented indexed product by `U` as a functor of the valued copresheaf variable. -/
@[stacks 0B15 "opposite indexed-product functoriality"]
def functor : (D ⥤ C) ⥤ (D ⥤ C) where
  obj V := indexedProd.op U V
  map f := hom U f
  map_id V := hom.id U V
  map_comp f g := hom.comp U f g

end ObjectVariableFunctor

section IndexVariableFunctor

variable (V : D ⥤ C) [HasIndexedPowers.Op.{i, w, d, v, u} V]

/-- Opposite-oriented indexed product with fixed valued copresheaf as a contravariant functor of
its indexing presheaf. -/
@[stacks 0B15 "opposite indexed-product functor in the indexing variable"]
def indexFunctor : (Dᵒᵖ ⥤ Type w)ᵒᵖ ⥤ (D ⥤ C) where
  obj U := indexedProd.op U.unop V
  map f := indexHom V f.unop
  map_id U := indexHom.id V U.unop
  map_comp f g := indexHom.comp V g.unop f.unop

/-- The object part of the opposite-oriented `indexFunctor V` is indexed product by the
underlying indexing presheaf. -/
@[simp, stacks 0B15 "opposite indexed-product index-functor object formula"]
theorem indexFunctor.obj (U : (Dᵒᵖ ⥤ Type w)ᵒᵖ) :
    (indexFunctor V).obj U = indexedProd.op U.unop V := sorry

/-- The map part of the opposite-oriented `indexFunctor V` is canonical contravariant
reindexing. -/
@[simp, stacks 0B15 "opposite indexed-product index-functor map formula"]
theorem indexFunctor.map {U W : (Dᵒᵖ ⥤ Type w)ᵒᵖ} (a : U ⟶ W) :
    (indexFunctor V).map a = indexHom V a.unop := sorry

end IndexVariableFunctor

section IndexNaturalTransformation

variable {U W : Dᵒᵖ ⥤ Type w}
variable [HasIndexedProds.Op U C] [HasIndexedProds.Op W C]

/-- A morphism of presheaves of indices induces a natural transformation between the associated
opposite-oriented indexed-product functors in the reverse direction. -/
@[stacks 0B15 "opposite indexed-product functoriality in the indexing variable"]
def indexHom.natTrans (a : U ⟶ W) :
    functor (C := C) W ⟶ functor (C := C) U where
  app V := indexHom V a
  naturality := fun _ _ f ↦ indexHom.naturality a f

/-- The component of an opposite-oriented indexed-product index natural transformation. -/
@[simp, stacks 0B15 "opposite indexed-product index natural-transformation component"]
theorem indexHom.natTrans.app (a : U ⟶ W) (V : D ⥤ C) :
    (indexHom.natTrans (C := C) a).app V = indexHom V a := sorry

/-- The opposite-oriented index natural transformation associated to an identity is the
identity. -/
@[simp, stacks 0B15 "opposite indexed-product index natural-transformation identity"]
theorem indexHom.natTrans.id (U : Dᵒᵖ ⥤ Type w) [HasIndexedProds.Op U C] :
    indexHom.natTrans (C := C) (𝟙 U) = 𝟙 (functor (C := C) U) := sorry

/-- Opposite-oriented index natural transformations reverse composition. -/
@[stacks 0B15 "opposite indexed-product index natural-transformation composition"]
theorem indexHom.natTrans.comp {U W X : Dᵒᵖ ⥤ Type w}
    [HasIndexedProds.Op U C] [HasIndexedProds.Op W C] [HasIndexedProds.Op X C]
    (a : U ⟶ W) (b : W ⟶ X) :
    indexHom.natTrans (C := C) (a ≫ b) =
      indexHom.natTrans (C := C) b ≫ indexHom.natTrans (C := C) a := sorry

end IndexNaturalTransformation

section Bifunctor

variable {E : Type j} [Category.{e} E]
variable (K : E ⥤ Dᵒᵖ ⥤ Type w) [HasIndexedProds.Op.OfIndex K C]

/-- Identity law for opposite-oriented indexed-product transformations along an indexing
functor. -/
@[stacks 0B15 "opposite indexed-product bifunctor identity"]
theorem bifunctor.map_id (x : Eᵒᵖ) :
    indexHom.natTrans (C := C) (K.map (𝟙 x.unop)) =
      𝟙 (functor (C := C) (K.obj x.unop)) := sorry

/-- Composition law for opposite-oriented indexed-product transformations along an indexing
functor. -/
@[stacks 0B15 "opposite indexed-product bifunctor composition"]
theorem bifunctor.map_comp {x y z : Eᵒᵖ} (f : x ⟶ y) (g : y ⟶ z) :
    indexHom.natTrans (C := C) (K.map (f ≫ g).unop) =
      indexHom.natTrans (C := C) (K.map f.unop) ≫
        indexHom.natTrans (C := C) (K.map g.unop) := sorry

/-- The opposite-oriented indexed product is a curried bifunctor, contravariant in an indexing
functor drawn from `K` and covariant in the valued copresheaf. -/
@[stacks 0B15 "opposite indexed-product bifunctor"]
def bifunctor : Eᵒᵖ ⥤ (D ⥤ C) ⥤ (D ⥤ C) where
  obj x := functor (C := C) (K.obj x.unop)
  map f := indexHom.natTrans (C := C) (K.map f.unop)
  map_id x := bifunctor.map_id (C := C) K x
  map_comp f g := bifunctor.map_comp (C := C) K f g

/-- Evaluating the opposite-oriented indexed-product bifunctor on both variables gives the
corresponding indexed product. -/
@[simp, stacks 0B15 "opposite indexed-product bifunctor object formula"]
theorem bifunctor.obj_obj (x : Eᵒᵖ) (V : D ⥤ C) :
    ((bifunctor (C := C) K).obj x).obj V = indexedProd.op (K.obj x.unop) V := sorry

/-- The indexing-variable map of the opposite-oriented indexed-product bifunctor is canonical
contravariant reindexing. -/
@[simp, stacks 0B15 "opposite indexed-product bifunctor map formula"]
theorem bifunctor.map_app {x y : Eᵒᵖ} (f : x ⟶ y) (V : D ⥤ C) :
    ((bifunctor (C := C) K).map f).app V = indexHom V (K.map f.unop) := sorry

end Bifunctor

end indexedProd.op

end CategoryTheory.Functor
