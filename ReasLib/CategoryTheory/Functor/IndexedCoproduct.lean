/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import ReasLib.CategoryTheory.Functor.Objwise
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Indexed coproduct diagram

Given a diagram `U : J ⥤ Type w` (an indexing diagram) and a diagram `V : J ⥤ C`
valued in a category with sufficient coproducts, the **indexed coproduct diagram**
`Functor.indexedCoprod U V` is the diagram `J ⥤ C` whose value at `Δ` is the coproduct
of `U.obj Δ` copies of `V.obj Δ`, with structure maps given by reindexing via `U` and
postcomposing via `V`.

This is the maximally general form of the tensor/copower construction used for simplicial
objects. The simplicial specialization appears in
`AlgebraicTopology.SimplicialObject.Copower`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w i d v u j e

namespace CategoryTheory.Functor

variable {J : Type i} [Category.{d} J] {C : Type u} [Category.{v} C]

/-- `HasIndexedCoprod U V` records the degreewise coproducts used by `indexedCoprod U V`.
Bundling the degreewise owners keeps typeclass search from unfolding a dependent function of
`HasCoproduct` goals at every use site. -/
@[stacks 017C "fixed-diagram indexed coproduct"]
class HasIndexedCoprod (U : J ⥤ Type w) (V : J ⥤ C) : Prop where
  /-- The coproduct used in degree `Delta`. -/
  hasCoproduct (Delta : J) : HasCoproduct (fun _ : U.obj Delta ↦ V.obj Delta)

/-- `HasIndexedCoprods U C` says that `indexedCoprod U V` exists for every `C`-valued
diagram `V`. -/
@[stacks 017C "fixed-index indexed coproducts"]
class HasIndexedCoprods (U : J ⥤ Type w) (C : Type u) [Category.{v} C] : Prop where
  /-- The indexed coproducts of any `C`-valued diagram by `U`. -/
  hasIndexedCoprod (V : J ⥤ C) : HasIndexedCoprod U V

/-- `HasIndexedCopowers V` says that `indexedCoprod U V` exists for every Type-valued
diagram `U`. This is the fixed-valued-functor counterpart of `HasIndexedCoprods`. -/
@[stacks 017C "fixed-object indexed copowers"]
class HasIndexedCopowers (V : J ⥤ C) : Prop where
  /-- The indexed coproduct of `V` by any Type-valued diagram. -/
  hasIndexedCoprod (U : J ⥤ Type w) : HasIndexedCoprod U V

namespace HasIndexedCoprod

/-- A bundled indexed-coproduct hypothesis supplies its coproduct in every degree. -/
@[stacks 017C "degreewise coproduct from fixed indexed-coproduct data"]
instance (priority := 100) hasCoproductInstance (U : J ⥤ Type w) (V : J ⥤ C)
    [HasIndexedCoprod U V] (Delta : J) :
    HasCoproduct (fun _ : U.obj Delta ↦ V.obj Delta) :=
  HasIndexedCoprod.hasCoproduct Delta

/-- A fixed indexed-coproduct owner restricts along any functor by precomposition in both
variables.  The low priority lets an owner stated directly on the restricted functors win. -/
@[stacks 017C "restriction of fixed indexed-coproduct existence"]
instance (priority := 40) comp {E : Type j} [Category.{e} E]
    (K : E ⥤ J) (U : J ⥤ Type w) (V : J ⥤ C)
    [HasIndexedCoprod U V] :
    HasIndexedCoprod (K ⋙ U) (K ⋙ V) :=
  ⟨fun X ↦ HasIndexedCoprod.hasCoproduct (U := U) (V := V) (K.obj X)⟩

/-- Finite coproducts supply an indexed coproduct for a degreewise finite indexing functor. -/
@[stacks 017C "finite indexed-coproduct existence"]
noncomputable instance ofFiniteCoproducts [HasFiniteCoproducts C]
    (U : J ⥤ Type w) (V : J ⥤ C) [U.ObjFinite] :
    HasIndexedCoprod U V := ⟨fun _ ↦ inferInstance⟩

end HasIndexedCoprod

namespace HasIndexedCoprods

/-- A uniform indexed-coproduct hypothesis specializes to every valued diagram. -/
@[stacks 017C "specialization of uniform indexed-coproduct data"]
instance (priority := 100) hasIndexedCoprodInstance (U : J ⥤ Type w) (C : Type u)
    [Category.{v} C] [HasIndexedCoprods U C] (V : J ⥤ C) : HasIndexedCoprod U V :=
  HasIndexedCoprods.hasIndexedCoprod V

/-- Finite coproducts supply indexed coproducts uniformly for a degreewise finite indexing
functor. -/
@[stacks 017C "uniform finite indexed-coproduct existence"]
noncomputable instance ofFiniteCoproducts [HasFiniteCoproducts C]
    (U : J ⥤ Type w) [U.ObjFinite] : HasIndexedCoprods U C :=
  ⟨fun V ↦ HasIndexedCoprod.ofFiniteCoproducts U V⟩

/-- `HasIndexedCoprods.OfIndex K C` records indexed coproducts for every indexing functor in
the image of `K`, uniformly in the `C`-valued diagram. This is the exact existence owner for
`indexedCoprod.bifunctor K`. -/
@[stacks 017C "indexed coproducts along an indexing functor"]
class OfIndex {E : Type j} [Category.{e} E]
    (K : E ⥤ (J ⥤ Type w)) (C : Type u) [Category.{v} C] : Prop where
  /-- Every object in the image of `K` admits indexed coproducts of all `C`-valued
  diagrams. -/
  hasIndexedCoprods (X : E) : HasIndexedCoprods (K.obj X) C

end HasIndexedCoprods

attribute [instance] HasIndexedCoprods.OfIndex.hasIndexedCoprods

namespace HasIndexedCoprods.OfIndex

/-- Indexed coproducts along the identity indexing functor supply indexed coproducts for every
indexing functor. This low-priority bridge handles goals where reducing `Functor.id.obj` erases
the indexing functor needed to select the generic projection instance. -/
@[stacks 017C "indexed coproducts from the identity indexing functor"]
instance (priority := 40) identity (C : Type u) [Category.{v} C]
    [self : HasIndexedCoprods.OfIndex (𝟭 (J ⥤ Type w)) C]
    (U : J ⥤ Type w) : HasIndexedCoprods U C :=
  self.hasIndexedCoprods U

end HasIndexedCoprods.OfIndex

namespace HasIndexedCopowers

/-- A fixed-object indexed-copower owner specializes to every indexing diagram. -/
@[stacks 017C "specialization of fixed-object indexed copowers"]
instance (priority := 50) hasIndexedCoprodInstance (V : J ⥤ C)
    [self : HasIndexedCopowers.{w} V] (U : J ⥤ Type w) : HasIndexedCoprod U V :=
  self.hasIndexedCoprod U

/-- A category with all coproducts supplies indexed copowers of every fixed valued diagram. -/
@[stacks 017C "fixed-object indexed copowers from coproducts"]
instance ofCoproducts [HasCoproducts.{w} C] (V : J ⥤ C) :
    HasIndexedCopowers.{w} V :=
  ⟨fun _ ↦ ⟨fun _ ↦ inferInstance⟩⟩

end HasIndexedCopowers

/-- A constant indexed coproduct supplies the coproduct of the corresponding constant family in
each degree. This bridge keeps injection APIs readable as `fun _ ↦ X` while allowing the
canonical `HasIndexedCoprod` interface to remain the sole existence input. -/
@[stacks 017C "constant-family indexed coproduct instance"]
instance indexedCoprod.hasCoproduct_const (U : J ⥤ Type w) (X : C) (Delta : J)
    [h : HasIndexedCoprod U ((Functor.const J).obj X)] :
    HasCoproduct (fun _ : U.obj Delta ↦ X) :=
  HasIndexedCoprod.hasCoproduct
    (U := U) (V := (Functor.const J).obj X) Delta

variable (U : J ⥤ Type w) (V : J ⥤ C)
variable [HasIndexedCoprod U V]

/-- The degreewise reindexing morphism underlying the indexed coproduct diagram. -/
@[stacks 017C "indexed-coproduct reindexing morphism"]
def indexedCoprod.mapHom {Δ₁ Δ₂ : J} (f : Δ₁ ⟶ Δ₂) :
    (∐ fun _ : U.obj Δ₁ ↦ V.obj Δ₁) ⟶ (∐ fun _ : U.obj Δ₂ ↦ V.obj Δ₂) :=
  Sigma.map' (U.map f) (fun _ ↦ V.map f)

/-- Indexed-coproduct reindexing preserves identity morphisms. -/
@[stacks 017C "indexed-coproduct reindexing identity law"]
theorem indexedCoprod.mapHom.id (Δ : J) :
    indexedCoprod.mapHom U V (𝟙 Δ) =
      𝟙 (∐ fun _ : U.obj Δ ↦ V.obj Δ) := sorry

/-- Indexed-coproduct reindexing preserves composition. -/
@[stacks 017C "indexed-coproduct reindexing composition law"]
theorem indexedCoprod.mapHom.comp {Δ₁ Δ₂ Δ₃ : J}
    (f : Δ₁ ⟶ Δ₂) (g : Δ₂ ⟶ Δ₃) :
    indexedCoprod.mapHom U V (f ≫ g) =
      indexedCoprod.mapHom U V f ≫ indexedCoprod.mapHom U V g := sorry

/-- The indexed coproduct diagram: given `U : J ⥤ Type w` and `V : J ⥤ C`, its value
at `Δ : J` is the coproduct `∐ (fun _ : U.obj Δ ↦ V.obj Δ)`, with structure maps
`Sigma.map' (U.map f) (fun _ ↦ V.map f)`. -/
@[stacks 017C "set-valued diagram indexed coproduct"]
def indexedCoprod : J ⥤ C where
  obj Δ := ∐ (fun _ : U.obj Δ ↦ V.obj Δ)
  map f := indexedCoprod.mapHom U V f
  map_id Δ := indexedCoprod.mapHom.id U V Δ
  map_comp f g := indexedCoprod.mapHom.comp U V f g

/-- The value of an indexed coproduct is the corresponding coproduct in the target category. -/
@[simp, stacks 017C "indexed-coproduct object formula"]
theorem indexedCoprod.obj (Δ : J) :
    (indexedCoprod U V).obj Δ = ∐ (fun _ : U.obj Δ ↦ V.obj Δ) := sorry

/-- The structure map of an indexed coproduct is the reindexing coproduct map. -/
@[simp, stacks 017C "indexed-coproduct map formula"]
theorem indexedCoprod.map {Δ₁ Δ₂ : J} (f : Δ₁ ⟶ Δ₂) :
    (indexedCoprod U V).map f = Sigma.map' (U.map f) (fun _ ↦ V.map f) := sorry

/-- An injection into an indexed coproduct followed by its structure map is the corresponding
injection after reindexing, followed by the structure map of the valued diagram. -/
@[stacks 017C "indexed-coproduct structure-map injection formula"]
theorem indexedCoprod.ι.map {Δ₁ Δ₂ : J} (f : Δ₁ ⟶ Δ₂) (u : U.obj Δ₁) :
    Sigma.ι (fun _ : U.obj Δ₁ ↦ V.obj Δ₁) u ≫ (indexedCoprod U V).map f =
      V.map f ≫ Sigma.ι (fun _ : U.obj Δ₂ ↦ V.obj Δ₂) (U.map f u) := sorry

/-- A morphism out of an indexed coproduct is componentwise natural with respect to its
coproduct injections. -/
@[stacks 017C "indexed-coproduct morphism naturality"]
theorem indexedCoprod.hom_naturality {X : J ⥤ C}
    (h : indexedCoprod U V ⟶ X) {Δ₁ Δ₂ : J} (f : Δ₁ ⟶ Δ₂) (u : U.obj Δ₁) :
    CommSq
      (V.map f)
      (Sigma.ι (fun _ : U.obj Δ₁ ↦ V.obj Δ₁) u ≫ h.app Δ₁)
      (Sigma.ι (fun _ : U.obj Δ₂ ↦ V.obj Δ₂) (U.map f u) ≫ h.app Δ₂)
      (X.map f) := sorry

/-- Two morphisms out of an indexed coproduct are equal when they agree after every
degreewise coproduct injection. -/
@[ext, stacks 017C "indexed-coproduct morphism extensionality"]
theorem indexedCoprod.hom_ext {X : J ⥤ C}
    {f g : indexedCoprod U V ⟶ X}
    (h : ∀ (Δ : J) (u : U.obj Δ),
      Sigma.ι (fun _ : U.obj Δ ↦ V.obj Δ) u ≫ f.app Δ =
        Sigma.ι (fun _ : U.obj Δ ↦ V.obj Δ) u ≫ g.app Δ) :
    f = g := sorry

namespace indexedCoprod

section ObjectVariable

variable (U : J ⥤ Type w) {V W : J ⥤ C}

/-- The raw component of the indexed-coproduct morphism induced by a morphism in the valued
diagram variable. -/
@[stacks 017C "indexed-coproduct induced component"]
def homApp [HasIndexedCoprod U V] [HasIndexedCoprod U W]
    (f : V ⟶ W) (Δ : J) :
    (indexedCoprod U V).obj Δ ⟶ (indexedCoprod U W).obj Δ :=
  Limits.Sigma.map (fun _ : U.obj Δ ↦ f.app Δ)

/-- The induced indexed-coproduct components form a natural family. -/
@[stacks 017C "indexed-coproduct induced naturality"]
theorem homApp.naturality [HasIndexedCoprod U V] [HasIndexedCoprod U W]
    (f : V ⟶ W) {Δ₁ Δ₂ : J} (g : Δ₁ ⟶ Δ₂) :
    (indexedCoprod U V).map g ≫ homApp U f Δ₂ =
      homApp U f Δ₁ ≫ (indexedCoprod U W).map g := sorry

/-- A morphism of valued diagrams induces a morphism between their indexed coproducts. -/
@[stacks 017C "indexed-coproduct induced morphism"]
def hom [HasIndexedCoprod U V] [HasIndexedCoprod U W]
    (f : V ⟶ W) : indexedCoprod U V ⟶ indexedCoprod U W where
  app := homApp U f
  naturality := fun _ _ g ↦ homApp.naturality U f g

/-- The component of the morphism induced between indexed coproducts. -/
@[simp, stacks 017C "indexed-coproduct induced component formula"]
theorem hom_app [HasIndexedCoprod U V] [HasIndexedCoprod U W]
    (f : V ⟶ W) (Δ : J) :
    (hom U f).app Δ = homApp U f Δ := sorry

/-- Evaluation of an induced indexed-coproduct morphism on a coproduct injection. -/
@[reassoc (attr := simp), stacks 017C "indexed-coproduct induced injection formula"]
theorem hom.ι
    [HasIndexedCoprod U V] [HasIndexedCoprod U W]
    (f : V ⟶ W) (Δ : J) (u : U.obj Δ) :
    Sigma.ι (fun _ : U.obj Δ ↦ V.obj Δ) u ≫ (hom U f).app Δ =
      f.app Δ ≫ Sigma.ι (fun _ : U.obj Δ ↦ W.obj Δ) u := sorry

/-- Indexed coproducts preserve identity morphisms in the valued variable. -/
@[simp, stacks 017C "indexed-coproduct induced identity"]
theorem hom.id (V : J ⥤ C) [HasIndexedCoprod U V] :
    hom U (𝟙 V) = 𝟙 (indexedCoprod U V) := sorry

/-- Indexed coproducts preserve composition in the valued variable. -/
@[stacks 017C "indexed-coproduct induced composition"]
theorem hom.comp {V W X : J ⥤ C}
    [HasIndexedCoprod U V] [HasIndexedCoprod U W] [HasIndexedCoprod U X]
    (f : V ⟶ W) (g : W ⟶ X) :
    hom U (f ≫ g) = hom U f ≫ hom U g := sorry

end ObjectVariable

section IndexVariable

variable {U₁ U₂ : J ⥤ Type w} (V : J ⥤ C)

/-- The raw component of the indexed-coproduct morphism induced by a morphism in the
indexing-diagram variable. -/
@[stacks 017C "indexed-coproduct index-map component"]
def indexHomApp [HasIndexedCoprod U₁ V] [HasIndexedCoprod U₂ V]
    (a : U₁ ⟶ U₂) (Delta : J) :
    (indexedCoprod U₁ V).obj Delta ⟶ (indexedCoprod U₂ V).obj Delta :=
  Sigma.map' (a.app Delta) (fun _ ↦ 𝟙 (V.obj Delta))

/-- The components induced by a morphism of indexing diagrams form a natural family. -/
@[stacks 017C "indexed-coproduct index-map naturality"]
theorem indexHomApp.naturality [HasIndexedCoprod U₁ V] [HasIndexedCoprod U₂ V]
    (a : U₁ ⟶ U₂) {Delta₁ Delta₂ : J} (f : Delta₁ ⟶ Delta₂) :
    (indexedCoprod U₁ V).map f ≫ indexHomApp V a Delta₂ =
      indexHomApp V a Delta₁ ≫ (indexedCoprod U₂ V).map f := sorry

/-- A morphism of indexing diagrams induces a morphism between the corresponding indexed
coproducts. -/
@[stacks 017C "indexed-coproduct morphism in the indexing variable"]
def indexHom [HasIndexedCoprod U₁ V] [HasIndexedCoprod U₂ V]
    (a : U₁ ⟶ U₂) : indexedCoprod U₁ V ⟶ indexedCoprod U₂ V where
  app := indexHomApp V a
  naturality := fun {_ _} f ↦ indexHomApp.naturality V a f

/-- The component of a morphism induced in the indexing-diagram variable. -/
@[simp, stacks 017C "indexed-coproduct index-map component formula"]
theorem indexHom_app [HasIndexedCoprod U₁ V] [HasIndexedCoprod U₂ V]
    (a : U₁ ⟶ U₂) (Delta : J) :
    (indexHom V a).app Delta = indexHomApp V a Delta := sorry

/-- An index-induced morphism sends each coproduct injection to the injection selected by the
image of its index. -/
@[reassoc (attr := simp), stacks 017C "indexed-coproduct index-map injection formula"]
theorem indexHom.ι [HasIndexedCoprod U₁ V] [HasIndexedCoprod U₂ V]
    (a : U₁ ⟶ U₂) (Delta : J) (u : U₁.obj Delta) :
    Sigma.ι (fun _ : U₁.obj Delta ↦ V.obj Delta) u ≫ (indexHom V a).app Delta =
      Sigma.ι (fun _ : U₂.obj Delta ↦ V.obj Delta) (a.app Delta u) := sorry

/-- Indexed coproducts preserve identity morphisms in the indexing-diagram variable. -/
@[simp, stacks 017C "indexed-coproduct index-map identity"]
theorem indexHom.id (U : J ⥤ Type w) [HasIndexedCoprod U V] :
    indexHom V (𝟙 U) = 𝟙 (indexedCoprod U V) := sorry

/-- Indexed coproducts preserve composition in the indexing-diagram variable. -/
@[stacks 017C "indexed-coproduct index-map composition"]
theorem indexHom.comp {U₁ U₂ U₃ : J ⥤ Type w}
    [HasIndexedCoprod U₁ V] [HasIndexedCoprod U₂ V] [HasIndexedCoprod U₃ V]
    (a : U₁ ⟶ U₂) (b : U₂ ⟶ U₃) :
    indexHom V (a ≫ b) = indexHom V a ≫ indexHom V b := sorry

end IndexVariable

section ObjectVariableFunctor

variable (U : J ⥤ Type w) [HasIndexedCoprods U C]

/-- Indexed coproduct by `U` as a functor of the valued diagram variable. -/
@[stacks 017C "indexed-coproduct functoriality"]
def functor : (J ⥤ C) ⥤ (J ⥤ C) where
  obj V := indexedCoprod U V
  map f := hom U f
  map_id V := hom.id U V
  map_comp f g := hom.comp U f g

end ObjectVariableFunctor

section IndexVariableFunctor

variable (V : J ⥤ C) [HasIndexedCopowers.{w} V]

/-- Indexed coproduct with valued diagram `V` as a functor of the indexing-diagram
variable. -/
@[stacks 017C "indexed-coproduct functor in the indexing variable"]
def indexFunctor : (J ⥤ Type w) ⥤ (J ⥤ C) where
  obj U := indexedCoprod U V
  map a := indexHom V a
  map_id U := indexHom.id V U
  map_comp a b := indexHom.comp V a b

/-- The object part of `indexFunctor V` is indexed coproduct by the given indexing
diagram. -/
@[simp, stacks 017C "indexed-coproduct index-functor object formula"]
theorem indexFunctor.obj (U : J ⥤ Type w) :
    (indexFunctor V).obj U = indexedCoprod U V := sorry

/-- The map part of `indexFunctor V` is induced by the indexing-diagram morphism. -/
@[simp, stacks 017C "indexed-coproduct index-functor map formula"]
theorem indexFunctor.map {U₁ U₂ : J ⥤ Type w} (a : U₁ ⟶ U₂) :
    (indexFunctor V).map a = indexHom V a := sorry

end IndexVariableFunctor

section MixedVariable

variable {U₁ U₂ : J ⥤ Type w} {V W : J ⥤ C}

/-- Reindexing an indexed coproduct is natural in the valued-diagram variable. -/
@[stacks 017C "indexed-coproduct variable interchange"]
theorem indexHom.naturality
    [HasIndexedCoprod U₁ V] [HasIndexedCoprod U₁ W]
    [HasIndexedCoprod U₂ V] [HasIndexedCoprod U₂ W]
    (a : U₁ ⟶ U₂) (f : V ⟶ W) :
    hom U₁ f ≫ indexHom W a = indexHom V a ≫ hom U₂ f := sorry

end MixedVariable

section IndexNaturalTransformation

variable {U₁ U₂ : J ⥤ Type w}
variable [HasIndexedCoprods U₁ C] [HasIndexedCoprods U₂ C]

/-- A morphism of indexing diagrams induces a natural transformation between the
corresponding indexed-coproduct functors. -/
@[stacks 017C "indexed-coproduct natural transformation in the indexing variable"]
def indexHom.natTrans (a : U₁ ⟶ U₂) :
    functor (C := C) U₁ ⟶ functor (C := C) U₂ where
  app V := indexHom V a
  naturality := fun {_ _} f ↦ indexHom.naturality a f

/-- The component of the natural transformation induced by an indexing-diagram morphism. -/
@[simp, stacks 017C "indexed-coproduct index natural-transformation component"]
theorem indexHom.natTrans.app (a : U₁ ⟶ U₂) (V : J ⥤ C) :
    (indexHom.natTrans (C := C) a).app V = indexHom V a := sorry

/-- The indexing natural transformation associated to an identity is the identity. -/
@[simp, stacks 017C "indexed-coproduct index natural-transformation identity"]
theorem indexHom.natTrans.id (U : J ⥤ Type w) [HasIndexedCoprods U C] :
    indexHom.natTrans (C := C) (𝟙 U) = 𝟙 (functor (C := C) U) := sorry

/-- Indexing natural transformations preserve composition. -/
@[stacks 017C "indexed-coproduct index natural-transformation composition"]
theorem indexHom.natTrans.comp {U₁ U₂ U₃ : J ⥤ Type w}
    [HasIndexedCoprods U₁ C] [HasIndexedCoprods U₂ C] [HasIndexedCoprods U₃ C]
    (a : U₁ ⟶ U₂) (b : U₂ ⟶ U₃) :
    indexHom.natTrans (C := C) (a ≫ b) =
      indexHom.natTrans (C := C) a ≫ indexHom.natTrans (C := C) b := sorry

end IndexNaturalTransformation

section Bifunctor

variable {E : Type j} [Category.{e} E]
variable (K : E ⥤ (J ⥤ Type w)) [HasIndexedCoprods.OfIndex K C]

/-- Identity law for index-variable natural transformations along an indexing functor. -/
@[stacks 017C "indexed-coproduct bifunctor identity"]
theorem bifunctor.map_id (X : E) :
    indexHom.natTrans (C := C) (K.map (𝟙 X)) =
      𝟙 (functor (C := C) (K.obj X)) := sorry

/-- Composition law for index-variable natural transformations along an indexing functor. -/
@[stacks 017C "indexed-coproduct bifunctor composition"]
theorem bifunctor.map_comp {X Y Z : E} (f : X ⟶ Y) (g : Y ⟶ Z) :
    indexHom.natTrans (C := C) (K.map (f ≫ g)) =
      indexHom.natTrans (C := C) (K.map f) ≫
        indexHom.natTrans (C := C) (K.map g) := sorry

/-- Indexed coproduct as a curried bifunctor, with the indexing variable restricted along
`K`. -/
@[stacks 017C "indexed-coproduct bifunctor"]
def bifunctor : E ⥤ (J ⥤ C) ⥤ (J ⥤ C) where
  obj X := functor (C := C) (K.obj X)
  map f := indexHom.natTrans (C := C) (K.map f)
  map_id X := bifunctor.map_id (C := C) K X
  map_comp f g := bifunctor.map_comp (C := C) K f g

/-- Evaluating the indexed-coproduct bifunctor on both variables gives the corresponding
indexed coproduct. -/
@[simp, stacks 017C "indexed-coproduct bifunctor object formula"]
theorem bifunctor.obj_obj (X : E) (V : J ⥤ C) :
    ((bifunctor (C := C) K).obj X).obj V = indexedCoprod (K.obj X) V := sorry

/-- The component of the indexed-coproduct bifunctor on a morphism in its indexing
variable. -/
@[simp, stacks 017C "indexed-coproduct bifunctor map formula"]
theorem bifunctor.map_app {X Y : E} (f : X ⟶ Y) (V : J ⥤ C) :
    ((bifunctor (C := C) K).map f).app V = indexHom V (K.map f) := sorry

end Bifunctor

end indexedCoprod

end CategoryTheory.Functor
