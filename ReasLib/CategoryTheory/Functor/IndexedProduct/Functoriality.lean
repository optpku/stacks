/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Functor.IndexedProduct.Basic

/-!
@stack 0B15

# Indexed products of presheaves

Given a covariant indexing functor `U : D ⥤ Type w` and a presheaf
`V : Dᵒᵖ ⥤ C`, this leaf constructs `Functor.indexedProd U V`.  It owns the standard
orientation's object and structure-map formulas, functoriality in both variables, and the
curried bifunctor.  Existence assumptions are owned by `IndexedProduct.Basic`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe i w d v u j e

namespace CategoryTheory.Functor

variable {D : Type i} [Category.{d} D] {C : Type u} [Category.{v} C]

/-- A constant indexed product supplies the product of the corresponding constant family in
each degree.  This bridge keeps projection APIs readable as `fun _ ↦ X` while allowing the
canonical `HasIndexedProd` interface to remain the sole existence input. -/
@[stacks 0B15 "constant-family indexed product instance"]
instance indexedProd.hasProduct_const (U : D ⥤ Type w) (X : C) (d : D)
    [h : HasIndexedProd U ((Functor.const Dᵒᵖ).obj X)] :
    HasProduct (fun _ : U.obj d ↦ X) :=
  HasIndexedProd.hasProduct (U := U) (V := (Functor.const Dᵒᵖ).obj X) d

variable (U : D ⥤ Type w) (V : Dᵒᵖ ⥤ C)
variable [HasIndexedProd U V]

/-- The degreewise reindexing morphism underlying the indexed product presheaf. -/
@[stacks 0B15 "indexed-product reindexing morphism"]
def indexedProd.mapHom {Δ₁ Δ₂ : Dᵒᵖ} (f : Δ₁ ⟶ Δ₂) :
    (∏ᶜ fun _ : U.obj (unop Δ₁) ↦ V.obj Δ₁) ⟶
      (∏ᶜ fun _ : U.obj (unop Δ₂) ↦ V.obj Δ₂) :=
  Pi.map' (U.map f.unop) (fun _ ↦ V.map f)

/-- Indexed-product reindexing preserves identity morphisms. -/
@[stacks 0B15 "indexed-product reindexing identity law"]
theorem indexedProd.mapHom.id (Δ : Dᵒᵖ) :
    indexedProd.mapHom U V (𝟙 Δ) =
      𝟙 (∏ᶜ fun _ : U.obj (unop Δ) ↦ V.obj Δ) := sorry

/-- Indexed-product reindexing preserves composition. -/
@[stacks 0B15 "indexed-product reindexing composition law"]
theorem indexedProd.mapHom.comp {Δ₁ Δ₂ Δ₃ : Dᵒᵖ}
    (f : Δ₁ ⟶ Δ₂) (g : Δ₂ ⟶ Δ₃) :
    indexedProd.mapHom U V (f ≫ g) =
      indexedProd.mapHom U V f ≫ indexedProd.mapHom U V g := sorry

/-- The indexed product presheaf: given `U : D ⥤ Type w` and `V : Dᵒᵖ ⥤ C`, its value at
`Δ : Dᵒᵖ` is the product `∏ᶜ (fun _ : U.obj (unop Δ) ↦ V.obj Δ)`, with structure maps
`Pi.map' (U.map f.unop) (fun _ ↦ V.map f)`. -/
@[stacks 0B15]
def indexedProd : Dᵒᵖ ⥤ C where
  obj Δ := ∏ᶜ (fun _ : U.obj (unop Δ) ↦ V.obj Δ)
  map f := indexedProd.mapHom U V f
  map_id Δ := indexedProd.mapHom.id U V Δ
  map_comp f g := indexedProd.mapHom.comp U V f g

/-- The structure map of `indexedProd U V` and the projection at `u : U.obj (unop Δ₂)` form
a commutative square: projecting after the structure map equals reindexing via `U` then
applying the structure map of `V`. -/
@[stacks 0B15 "indexed-product projection square"]
theorem indexedProd.map.π
    {Δ₁ Δ₂ : Dᵒᵖ} (f : Δ₁ ⟶ Δ₂) (u : U.obj (unop Δ₂)) :
    CommSq
      ((indexedProd U V).map f)
      (Pi.π (fun _ : U.obj (unop Δ₁) ↦ V.obj Δ₁) (U.map f.unop u))
      (Pi.π (fun _ : U.obj (unop Δ₂) ↦ V.obj Δ₂) u)
      (V.map f) := sorry

/-- A morphism into `indexedProd U V` is componentwise natural: the square formed by
the source structure map, the projection at `u`, and the target structure map commutes. -/
@[stacks 0B15 "indexed-product morphism naturality"]
theorem indexedProd.hom_naturality
    {X : Dᵒᵖ ⥤ C}
    (h : X ⟶ indexedProd U V)
    {Δ₁ Δ₂ : Dᵒᵖ} (f : Δ₁ ⟶ Δ₂) (u : U.obj (unop Δ₂)) :
    CommSq
      (X.map f)
      (h.app Δ₁ ≫ Pi.π (fun _ : U.obj (unop Δ₁) ↦ V.obj Δ₁) (U.map f.unop u))
      (h.app Δ₂ ≫ Pi.π (fun _ : U.obj (unop Δ₂) ↦ V.obj Δ₂) u)
      (V.map f) := sorry

/-- Morphisms into an indexed product presheaf are equal when all their degreewise product
projections agree. -/
@[ext, stacks 0B15 "indexed-product morphism extensionality"]
theorem indexedProd.hom_ext {X : Dᵒᵖ ⥤ C} {f g : X ⟶ indexedProd U V}
    (h : ∀ (Δ : Dᵒᵖ) (u : U.obj (unop Δ)),
      f.app Δ ≫ Pi.π (fun _ : U.obj (unop Δ) ↦ V.obj Δ) u =
        g.app Δ ≫ Pi.π (fun _ : U.obj (unop Δ) ↦ V.obj Δ) u) :
    f = g := sorry

/-- The value of an indexed product is the corresponding product in the target category. -/
@[simp, stacks 0B15 "indexed-product object formula"]
theorem indexedProd.obj (Δ : Dᵒᵖ) :
    (indexedProd U V).obj Δ = ∏ᶜ (fun _ : U.obj (unop Δ) ↦ V.obj Δ) := sorry

/-- The structure map of an indexed product reindexes factors and applies the valued functor. -/
@[simp, stacks 0B15 "indexed-product map formula"]
theorem indexedProd.map {Δ₁ Δ₂ : Dᵒᵖ} (f : Δ₁ ⟶ Δ₂) :
    (indexedProd U V).map f = Pi.map' (U.map f.unop) (fun _ ↦ V.map f) := sorry

namespace indexedProd

section ObjectVariable

variable (U : D ⥤ Type w) {V W : Dᵒᵖ ⥤ C}

/-- The raw component used to assemble the indexed-product morphism induced by a morphism in the
valued presheaf variable. -/
@[stacks 0B15 "indexed-product induced component"]
def homApp [HasIndexedProd U V] [HasIndexedProd U W]
    (f : V ⟶ W) (Δ : Dᵒᵖ) :
    (indexedProd U V).obj Δ ⟶ (indexedProd U W).obj Δ :=
  Limits.Pi.map (fun _ : U.obj (unop Δ) ↦ f.app Δ)

/-- The raw indexed-product components `homApp U f` form a natural family. -/
@[stacks 0B15 "indexed-product induced naturality"]
theorem homApp.naturality [HasIndexedProd U V] [HasIndexedProd U W]
    (f : V ⟶ W) {Δ₁ Δ₂ : Dᵒᵖ} (g : Δ₁ ⟶ Δ₂) :
    (indexedProd U V).map g ≫ homApp U f Δ₂ =
      homApp U f Δ₁ ≫ (indexedProd U W).map g := sorry

/-- A morphism of valued presheaves induces a morphism between their indexed products. -/
@[stacks 0B15 "indexed-product induced morphism"]
def hom [HasIndexedProd U V] [HasIndexedProd U W]
    (f : V ⟶ W) : indexedProd U V ⟶ indexedProd U W where
  app := homApp U f
  naturality := fun _ _ g ↦ homApp.naturality U f g

/-- The component of the bundled morphism induced between indexed products. -/
@[simp, stacks 0B15 "indexed-product induced component formula"]
theorem hom_app [HasIndexedProd U V] [HasIndexedProd U W]
    (f : V ⟶ W) (Δ : Dᵒᵖ) :
    (hom U f).app Δ = homApp U f Δ := sorry

/-- Evaluation of an induced indexed-product morphism at a product factor. -/
@[reassoc (attr := simp), stacks 0B15 "indexed-product induced projection formula"]
theorem hom.π
    [HasIndexedProd U V] [HasIndexedProd U W]
    (f : V ⟶ W) (Δ : Dᵒᵖ) (u : U.obj (unop Δ)) :
    (hom U f).app Δ ≫ Pi.π (fun _ : U.obj (unop Δ) ↦ W.obj Δ) u =
      Pi.π (fun _ : U.obj (unop Δ) ↦ V.obj Δ) u ≫ f.app Δ := sorry

/-- Indexed products preserve identity morphisms in the valued variable. -/
@[simp, stacks 0B15 "indexed-product induced identity"]
theorem hom.id (V : Dᵒᵖ ⥤ C) [HasIndexedProd U V] :
    hom U (𝟙 V) = 𝟙 (indexedProd U V) := sorry

/-- Indexed products preserve composition in the valued variable. -/
@[stacks 0B15 "indexed-product induced composition"]
theorem hom.comp {V W X : Dᵒᵖ ⥤ C}
    [HasIndexedProd U V] [HasIndexedProd U W] [HasIndexedProd U X]
    (f : V ⟶ W) (g : W ⟶ X) :
    hom U (f ≫ g) = hom U f ≫ hom U g := sorry

end ObjectVariable

section IndexVariable

variable {U W : D ⥤ Type w} (V : Dᵒᵖ ⥤ C)

/-- The raw component of the indexed-product morphism induced contravariantly by a morphism of
indexing functors. -/
@[stacks 0B15 "indexed-product index-map component"]
def indexHomApp [HasIndexedProd U V] [HasIndexedProd W V]
    (a : U ⟶ W) (Δ : Dᵒᵖ) :
    (indexedProd W V).obj Δ ⟶ (indexedProd U V).obj Δ :=
  Pi.lift (fun u : U.obj (unop Δ) ↦
    Pi.π (fun _ : W.obj (unop Δ) ↦ V.obj Δ) (a.app (unop Δ) u))

/-- The components induced contravariantly by an index morphism form a natural family. -/
@[stacks 0B15 "indexed-product index-map naturality"]
theorem indexHomApp.naturality [HasIndexedProd U V] [HasIndexedProd W V]
    (a : U ⟶ W) {Δ₁ Δ₂ : Dᵒᵖ} (f : Δ₁ ⟶ Δ₂) :
    (indexedProd W V).map f ≫ indexHomApp V a Δ₂ =
      indexHomApp V a Δ₁ ≫ (indexedProd U V).map f := sorry

/-- A morphism of indexing functors induces a morphism of indexed products in the reverse
direction. -/
@[stacks 0B15 "indexed-product morphism in the indexing variable"]
def indexHom [HasIndexedProd U V] [HasIndexedProd W V]
    (a : U ⟶ W) : indexedProd W V ⟶ indexedProd U V where
  app := indexHomApp V a
  naturality := fun _ _ f ↦ indexHomApp.naturality V a f

/-- The component of an indexed-product index morphism is its raw component. -/
@[simp, stacks 0B15 "indexed-product index-map component formula"]
theorem indexHom_app [HasIndexedProd U V] [HasIndexedProd W V]
    (a : U ⟶ W) (Δ : Dᵒᵖ) :
    (indexHom V a).app Δ = indexHomApp V a Δ := sorry

/-- An indexed-product index morphism reindexes every product projection. -/
@[reassoc (attr := simp), stacks 0B15 "indexed-product index-map projection formula"]
theorem indexHom.π [HasIndexedProd U V] [HasIndexedProd W V]
    (a : U ⟶ W) (Δ : Dᵒᵖ) (u : U.obj (unop Δ)) :
    (indexHom V a).app Δ ≫
        Pi.π (fun _ : U.obj (unop Δ) ↦ V.obj Δ) u =
      Pi.π (fun _ : W.obj (unop Δ) ↦ V.obj Δ) (a.app (unop Δ) u) := sorry

/-- Indexed-product reindexing sends an identity index morphism to an identity. -/
@[simp, stacks 0B15 "indexed-product index-map identity"]
theorem indexHom.id (U : D ⥤ Type w) [HasIndexedProd U V] :
    indexHom V (𝟙 U) = 𝟙 (indexedProd U V) := sorry

/-- Indexed-product reindexing reverses composition in the indexing variable. -/
@[stacks 0B15 "indexed-product index-map composition"]
theorem indexHom.comp {U W X : D ⥤ Type w}
    [HasIndexedProd U V] [HasIndexedProd W V] [HasIndexedProd X V]
    (a : U ⟶ W) (b : W ⟶ X) :
    indexHom V (a ≫ b) = indexHom V b ≫ indexHom V a := sorry

end IndexVariable

section MixedVariable

variable {U W : D ⥤ Type w} {V Z : Dᵒᵖ ⥤ C}

/-- Contravariant reindexing of indexed products commutes with covariant functoriality in the
valued presheaf. -/
@[stacks 0B15 "indexed-product variable interchange"]
theorem indexHom.naturality
    [HasIndexedProd U V] [HasIndexedProd U Z]
    [HasIndexedProd W V] [HasIndexedProd W Z]
    (a : U ⟶ W) (f : V ⟶ Z) :
    hom W f ≫ indexHom Z a = indexHom V a ≫ hom U f := sorry

end MixedVariable

section ObjectVariableFunctor

variable (U : D ⥤ Type w) [HasIndexedProds U C]

/-- Indexed product by `U` as a functor of the valued presheaf variable. -/
@[stacks 0B15 "indexed-product functoriality"]
def functor : (Dᵒᵖ ⥤ C) ⥤ (Dᵒᵖ ⥤ C) where
  obj V := indexedProd U V
  map f := hom U f
  map_id V := hom.id U V
  map_comp f g := hom.comp U f g

end ObjectVariableFunctor

section IndexVariableFunctor

variable (V : Dᵒᵖ ⥤ C) [HasIndexedPowers.{i, w, d, v, u} V]

/-- Indexed product with fixed valued presheaf as a contravariant functor of its indexing
functor. -/
@[stacks 0B15 "indexed-product functor in the indexing variable"]
def indexFunctor : (D ⥤ Type w)ᵒᵖ ⥤ (Dᵒᵖ ⥤ C) where
  obj U := indexedProd U.unop V
  map f := indexHom V f.unop
  map_id U := indexHom.id V U.unop
  map_comp f g := indexHom.comp V g.unop f.unop

/-- The object part of `indexFunctor V` is indexed product by the underlying indexing
functor. -/
@[simp, stacks 0B15 "indexed-product index-functor object formula"]
theorem indexFunctor.obj (U : (D ⥤ Type w)ᵒᵖ) :
    (indexFunctor V).obj U = indexedProd U.unop V := sorry

/-- The map part of `indexFunctor V` is the canonical contravariant reindexing map. -/
@[simp, stacks 0B15 "indexed-product index-functor map formula"]
theorem indexFunctor.map {U W : (D ⥤ Type w)ᵒᵖ} (a : U ⟶ W) :
    (indexFunctor V).map a = indexHom V a.unop := sorry

end IndexVariableFunctor

section IndexNaturalTransformation

variable {U W : D ⥤ Type w}
variable [HasIndexedProds U C] [HasIndexedProds W C]

/-- A morphism of indexing functors induces a natural transformation between the corresponding
indexed-product functors in the reverse direction. -/
@[stacks 0B15 "indexed-product functoriality in the indexing variable"]
def indexHom.natTrans (a : U ⟶ W) :
    functor (C := C) W ⟶ functor (C := C) U where
  app V := indexHom V a
  naturality := fun _ _ f ↦ indexHom.naturality a f

/-- The component of the natural transformation induced by an indexed-product index map. -/
@[simp, stacks 0B15 "indexed-product index natural-transformation component"]
theorem indexHom.natTrans.app (a : U ⟶ W) (V : Dᵒᵖ ⥤ C) :
    (indexHom.natTrans (C := C) a).app V = indexHom V a := sorry

/-- The index-variable natural transformation associated to an identity is the identity. -/
@[simp, stacks 0B15 "indexed-product index natural-transformation identity"]
theorem indexHom.natTrans.id (U : D ⥤ Type w) [HasIndexedProds U C] :
    indexHom.natTrans (C := C) (𝟙 U) = 𝟙 (functor (C := C) U) := sorry

/-- Index-variable natural transformations reverse composition. -/
@[stacks 0B15 "indexed-product index natural-transformation composition"]
theorem indexHom.natTrans.comp {U W X : D ⥤ Type w}
    [HasIndexedProds U C] [HasIndexedProds W C] [HasIndexedProds X C]
    (a : U ⟶ W) (b : W ⟶ X) :
    indexHom.natTrans (C := C) (a ≫ b) =
      indexHom.natTrans (C := C) b ≫ indexHom.natTrans (C := C) a := sorry

end IndexNaturalTransformation

section Bifunctor

variable {E : Type j} [Category.{e} E]
variable (K : E ⥤ D ⥤ Type w) [HasIndexedProds.OfIndex K C]

/-- Identity law for indexed-product natural transformations along an indexing functor. -/
@[stacks 0B15 "indexed-product bifunctor identity"]
theorem bifunctor.map_id (x : Eᵒᵖ) :
    indexHom.natTrans (C := C) (K.map (𝟙 x.unop)) =
      𝟙 (functor (C := C) (K.obj x.unop)) := sorry

/-- Composition law for indexed-product natural transformations along an indexing functor. -/
@[stacks 0B15 "indexed-product bifunctor composition"]
theorem bifunctor.map_comp {x y z : Eᵒᵖ} (f : x ⟶ y) (g : y ⟶ z) :
    indexHom.natTrans (C := C) (K.map (f ≫ g).unop) =
      indexHom.natTrans (C := C) (K.map f.unop) ≫
        indexHom.natTrans (C := C) (K.map g.unop) := sorry

/-- Indexed product is a curried bifunctor, contravariant in an indexing functor drawn from `K`
and covariant in the valued presheaf. -/
@[stacks 0B15 "indexed-product bifunctor"]
def bifunctor : Eᵒᵖ ⥤ (Dᵒᵖ ⥤ C) ⥤ (Dᵒᵖ ⥤ C) where
  obj x := functor (C := C) (K.obj x.unop)
  map f := indexHom.natTrans (C := C) (K.map f.unop)
  map_id x := bifunctor.map_id (C := C) K x
  map_comp f g := bifunctor.map_comp (C := C) K f g

/-- Evaluating the indexed-product bifunctor on both variables gives the corresponding indexed
product. -/
@[simp, stacks 0B15 "indexed-product bifunctor object formula"]
theorem bifunctor.obj_obj (x : Eᵒᵖ) (V : Dᵒᵖ ⥤ C) :
    ((bifunctor (C := C) K).obj x).obj V = indexedProd (K.obj x.unop) V := sorry

/-- The indexing-variable map of the indexed-product bifunctor is the canonical contravariant
reindexing map. -/
@[simp, stacks 0B15 "indexed-product bifunctor map formula"]
theorem bifunctor.map_app {x y : Eᵒᵖ} (f : x ⟶ y) (V : Dᵒᵖ ⥤ C) :
    ((bifunctor (C := C) K).map f).app V = indexHom V (K.map f.unop) := sorry

end Bifunctor

end indexedProd

end CategoryTheory.Functor
