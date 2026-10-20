/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.CosimplicialObject.Cotensor.Object
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Cotensor functoriality in the simplicial-set index

This leaf owns the contravariant index maps, their functorial packaging, and indexed families of
cotensor functors.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section

universe w v u e d

namespace CategoryTheory.CosimplicialObject

variable {C : Type u} [Category.{v} C]

namespace cotensor

section IndexVariable

variable {U W : SSet.{w}} (V : CosimplicialObject C)

/-- The raw component induced contravariantly on cotensors by a morphism of indexing simplicial
sets. -/
@[stacks 019V "cotensor index-map component"]
abbrev indexHomApp [HasCotensor U V] [HasCotensor W V]
    (a : U ⟶ W) (n : SimplexCategory) :
    (cotensor W V).obj n ⟶ (cotensor U V).obj n :=
  Functor.indexedProd.op.indexHomApp V a n

/-- The raw cotensor components induced by an indexing morphism form a natural family. -/
@[stacks 019V "cotensor index-map naturality"]
theorem indexHomApp.naturality [HasCotensor U V] [HasCotensor W V]
    (a : U ⟶ W) {m n : SimplexCategory} (f : m ⟶ n) :
    (cotensor W V).map f ≫ indexHomApp V a n =
      indexHomApp V a m ≫ (cotensor U V).map f := sorry

/-- A morphism `a : U ⟶ W` of indexing simplicial sets induces a cotensor morphism in the
reverse direction. -/
@[stacks 019V "cotensor morphism in the indexing variable"]
abbrev indexHom [HasCotensor U V] [HasCotensor W V]
    (a : U ⟶ W) : cotensor W V ⟶ cotensor U V :=
  Functor.indexedProd.op.indexHom V a

/-- The component of `cotensor.indexHom` is its corresponding raw component. -/
@[simp, stacks 019V "cotensor index-map component formula"]
theorem indexHom.app [HasCotensor U V] [HasCotensor W V]
    (a : U ⟶ W) (n : SimplexCategory) :
    (indexHom V a).app n = indexHomApp V a n := sorry

/-- A cotensor index morphism reindexes every product projection. -/
@[reassoc (attr := simp), stacks 019V "cotensor index-map projection formula"]
theorem indexHom.π [HasCotensor U V] [HasCotensor W V]
    (a : U ⟶ W) (n : SimplexCategory) (u : U.obj (op n)) :
    (indexHom V a).app n ≫
        Pi.π (fun _ : U.obj (op n) ↦ V.obj n) u =
      Pi.π (fun _ : W.obj (op n) ↦ V.obj n) (a.app (op n) u) := sorry

/-- Cotensor reindexing preserves identity indexing morphisms. -/
@[simp, stacks 019V "cotensor index-map identity"]
theorem indexHom.id (U : SSet.{w}) [HasCotensor U V] :
    indexHom V (𝟙 U) = 𝟙 (cotensor U V) := sorry

/-- Cotensor reindexing reverses composition in the indexing variable. -/
@[stacks 019V "cotensor index-map composition"]
theorem indexHom.comp {U W X : SSet.{w}}
    [HasCotensor U V] [HasCotensor W V] [HasCotensor X V]
    (a : U ⟶ W) (b : W ⟶ X) :
    indexHom V (a ≫ b) = indexHom V b ≫ indexHom V a := sorry

variable [V.HasCotensorsOf]

/-- Cotensoring a fixed cosimplicial object as a contravariant functor of the indexing
simplicial set. -/
@[stacks 019V "cotensor functor in the indexing variable"]
abbrev indexFunctor : SSet.{w}ᵒᵖ ⥤ CosimplicialObject C :=
  Functor.indexedProd.op.indexFunctor V

/-- The object part of `indexFunctor V` is cotensoring by the underlying simplicial set. -/
@[simp, stacks 019V "cotensor index-functor object formula"]
theorem indexFunctor.obj (U : SSet.{w}ᵒᵖ) :
    (indexFunctor V).obj U = cotensor U.unop V := sorry

/-- The map part of `indexFunctor V` is the canonical contravariant reindexing map. -/
@[simp, stacks 019V "cotensor index-functor map formula"]
theorem indexFunctor.map {U W : SSet.{w}ᵒᵖ} (a : U ⟶ W) :
    (indexFunctor V).map a = indexHom V a.unop := sorry

end IndexVariable

section MixedVariable

variable {U W : SSet.{w}} {V Z : CosimplicialObject C}

/-- Contravariant reindexing of cotensors commutes with functoriality in the cosimplicial-object
variable. -/
@[stacks 019V "cotensor variable interchange"]
theorem indexHom.naturality
    [HasCotensor U V] [HasCotensor U Z] [HasCotensor W V] [HasCotensor W Z]
    (a : U ⟶ W) (f : V ⟶ Z) :
    CommSq (cotensor.hom W f) (indexHom V a)
      (indexHom Z a) (cotensor.hom U f) := sorry

end MixedVariable

section IndexNaturalTransformation

variable {U W : SSet.{w}}
variable [HasCotensors U C] [HasCotensors W C]

/-- A morphism of indexing simplicial sets induces a natural transformation between the
associated cotensor functors in the reverse direction. -/
@[stacks 019V "cotensor functoriality in the indexing variable"]
abbrev indexHom.natTrans (a : U ⟶ W) :
    cotensor.functor (C := C) W ⟶ cotensor.functor (C := C) U :=
  Functor.indexedProd.op.indexHom.natTrans (C := C) a

/-- The component of the natural transformation induced by an indexing morphism. -/
@[simp, stacks 019V "cotensor index natural-transformation component"]
theorem indexHom.natTrans.app (a : U ⟶ W) (V : CosimplicialObject C) :
    (indexHom.natTrans (C := C) a).app V = indexHom V a := sorry

/-- The cotensor index natural transformation associated to an identity is the identity. -/
@[simp, stacks 019V "cotensor index natural-transformation identity"]
theorem indexHom.natTrans.id (U : SSet.{w}) [HasCotensors U C] :
    indexHom.natTrans (C := C) (𝟙 U) = 𝟙 (cotensor.functor (C := C) U) := sorry

/-- Cotensor index natural transformations reverse composition. -/
@[stacks 019V "cotensor index natural-transformation composition"]
theorem indexHom.natTrans.comp {U W X : SSet.{w}}
    [HasCotensors U C] [HasCotensors W C] [HasCotensors X C]
    (a : U ⟶ W) (b : W ⟶ X) :
    indexHom.natTrans (C := C) (a ≫ b) =
      indexHom.natTrans (C := C) b ≫ indexHom.natTrans (C := C) a := sorry

end IndexNaturalTransformation

section OfIndex

variable {D : Type d} [Category.{e} D]
variable (K : D ⥤ SSet.{w}) [HasCotensors.OfIndex K C]

/-- Identity law for cotensor transformations along an indexing functor. -/
@[stacks 019V "indexed cotensor functor identity"]
theorem ofIndex.map.id (d : Dᵒᵖ) :
    indexHom.natTrans (C := C) (K.map (𝟙 d.unop)) =
      𝟙 (cotensor.functor (C := C) (K.obj d.unop)) := sorry

/-- Composition law for cotensor transformations along an indexing functor. -/
@[stacks 019V "indexed cotensor functor composition"]
theorem ofIndex.map.comp {d₁ d₂ d₃ : Dᵒᵖ}
    (f : d₁ ⟶ d₂) (g : d₂ ⟶ d₃) :
    indexHom.natTrans (C := C) (K.map (f ≫ g).unop) =
      indexHom.natTrans (C := C) (K.map f.unop) ≫
        indexHom.natTrans (C := C) (K.map g.unop) := sorry

/-- Cotensor is a curried bifunctor, contravariant in simplicial sets drawn from `K` and
covariant in cosimplicial objects. -/
@[stacks 019V "cosimplicial cotensor bifunctor along an index"]
abbrev ofIndex : Dᵒᵖ ⥤ CosimplicialObject C ⥤ CosimplicialObject C :=
  Functor.indexedProd.op.bifunctor (C := C) K

/-- Evaluating `ofIndex K` on both variables gives the corresponding cotensor. -/
@[simp, stacks 019V "indexed cotensor object formula"]
theorem ofIndex.obj (d : Dᵒᵖ) (V : CosimplicialObject C) :
    ((ofIndex (C := C) K).obj d).obj V = cotensor (K.obj d.unop) V := sorry

/-- The action of `ofIndex K` on a morphism in the cosimplicial-object variable. -/
@[simp, stacks 019V "indexed cotensor object-variable map formula"]
theorem ofIndex.obj.map (d : Dᵒᵖ) {V W : CosimplicialObject C} (f : V ⟶ W) :
    ((ofIndex (C := C) K).obj d).map f = cotensor.hom (K.obj d.unop) f := sorry

/-- The component of `ofIndex K` on a morphism in its indexing variable. -/
@[simp, stacks 019V "indexed cotensor index-map formula"]
theorem ofIndex.map.app {d d' : Dᵒᵖ} (f : d ⟶ d') (V : CosimplicialObject C) :
    ((ofIndex (C := C) K).map f).app V = indexHom V (K.map f.unop) := sorry

end OfIndex

end cotensor

end CategoryTheory.CosimplicialObject
