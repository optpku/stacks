/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import ReasLib.CategoryTheory.Functor.Objwise
public import ReasLib.CategoryTheory.Limits.Shapes.PositivePowers
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Indexed-product existence

This leaf owns the fixed-object, uniform, and indexing-family existence classes for both
orientations of indexed products.  It also supplies the canonical restriction, finite-product,
positive-power, and all-product instances.  The actual indexed-product functors live in the
variance-specific `Functoriality` and `Op` leaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe i w d v u j e

namespace CategoryTheory.Functor

variable {D : Type i} [Category.{d} D] {C : Type u} [Category.{v} C]

/- The fixed-object interface is intentionally weaker than
`HasProductsOfShape (U.obj d) C`: the indexed product only asks for the
particular family `fun _ ↦ V.obj (Opposite.op d)`. -/
/-- `HasIndexedProd U V` records the degreewise products used by `indexedProd U V` for one fixed
indexing functor and one fixed presheaf.  Bundling these products keeps typeclass search from
unfolding a dependent function of `HasProduct` goals at every use site. -/
@[stacks 0B15 "fixed-presheaf indexed product"]
class HasIndexedProd (U : D ⥤ Type w) (V : Dᵒᵖ ⥤ C) : Prop where
  /-- The product used in degree `d`. -/
  hasProduct (d : D) : HasProduct (fun _ : U.obj d ↦ V.obj (Opposite.op d))

/-- `HasIndexedProds U C` says that `indexedProd U V` exists for every
`C`-valued presheaf `V`. -/
@[stacks 0B15 "fixed-index indexed products"]
class HasIndexedProds (U : D ⥤ Type w) (C : Type u) [Category.{v} C] : Prop where
  /-- The indexed products of any `C`-valued presheaf by `U`. -/
  hasIndexedProd (V : Dᵒᵖ ⥤ C) : HasIndexedProd U V

/-- `HasIndexedProd.Op U V` is the covariant variance of `HasIndexedProd`: it records the
degreewise products for a set-valued presheaf `U` and a `C`-valued copresheaf `V`. -/
@[stacks 0B15 "opposite-oriented indexed product"]
class HasIndexedProd.Op (U : Dᵒᵖ ⥤ Type w) (V : D ⥤ C) : Prop where
  /-- The product used in degree `d`. -/
  hasProduct (d : D) : HasProduct (fun _ : U.obj (Opposite.op d) ↦ V.obj d)

/-- `HasIndexedProds.Op U C` says that the opposite-oriented indexed product exists for every
`C`-valued copresheaf. -/
@[stacks 0B15 "opposite-oriented indexed products"]
class HasIndexedProds.Op (U : Dᵒᵖ ⥤ Type w) (C : Type u) [Category.{v} C] : Prop where
  /-- The opposite-oriented indexed products of any `C`-valued copresheaf by `U`. -/
  hasIndexedProd (V : D ⥤ C) : HasIndexedProd.Op U V

/-- `HasIndexedPowers V` says that `indexedProd U V` exists for every Type-valued covariant
indexing functor `U`. This is the fixed-valued-functor counterpart of `HasIndexedProds`. -/
@[stacks 0B15 "fixed-presheaf indexed powers"]
class HasIndexedPowers (V : Dᵒᵖ ⥤ C) : Prop where
  /-- The indexed product of `V` by any Type-valued covariant functor. -/
  hasIndexedProd (U : D ⥤ Type w) : HasIndexedProd U V

/-- `HasIndexedPowers.Op V` says that `indexedProd.op U V` exists for every Type-valued
presheaf `U`. -/
@[stacks 0B15 "fixed-copresheaf opposite indexed powers"]
class HasIndexedPowers.Op (V : D ⥤ C) : Prop where
  /-- The opposite-oriented indexed product of `V` by any Type-valued presheaf. -/
  hasIndexedProd (U : Dᵒᵖ ⥤ Type w) : HasIndexedProd.Op U V

/-- `HasIndexedProds.OfIndex K C` records indexed products for every indexing functor in the
image of `K` and every `C`-valued presheaf. -/
@[stacks 0B15 "indexed products along an indexing functor"]
class HasIndexedProds.OfIndex {E : Type j} [Category.{e} E]
    (K : E ⥤ D ⥤ Type w) (C : Type u) [Category.{v} C] : Prop where
  /-- Every value of `K` supports indexed products with all `C`-valued presheaves. -/
  hasIndexedProds (x : E) : HasIndexedProds (K.obj x) C

/-- `HasIndexedProds.Op.OfIndex K C` is the opposite-oriented indexed-product existence owner
along an indexing functor `K`. -/
@[stacks 0B15 "opposite indexed products along an indexing functor"]
class HasIndexedProds.Op.OfIndex {E : Type j} [Category.{e} E]
    (K : E ⥤ Dᵒᵖ ⥤ Type w) (C : Type u) [Category.{v} C] : Prop where
  /-- Every value of `K` supports opposite-oriented indexed products with all valued functors. -/
  hasIndexedProds (x : E) : HasIndexedProds.Op (K.obj x) C

namespace HasIndexedProd

/-- A bundled indexed-product hypothesis supplies its product in every degree. -/
@[stacks 0B15 "degreewise product from fixed indexed-product data"]
instance (priority := 100) hasProductInstance (U : D ⥤ Type w) (V : Dᵒᵖ ⥤ C)
    [HasIndexedProd U V] (d : D) :
    HasProduct (fun _ : U.obj d ↦ V.obj (Opposite.op d)) :=
  HasIndexedProd.hasProduct d

/-- A fixed indexed-product owner restricts along any functor by precomposition in both
variables.  The low priority lets an owner stated directly on the restricted functors win. -/
@[stacks 0B15 "restriction of fixed indexed-product existence"]
instance (priority := 40) comp {E : Type j} [Category.{e} E]
    (K : E ⥤ D) (U : D ⥤ Type w) (V : Dᵒᵖ ⥤ C)
    [HasIndexedProd U V] :
    HasIndexedProd (K ⋙ U) (K.op ⋙ V) :=
  ⟨fun X ↦ HasIndexedProd.hasProduct (U := U) (V := V) (K.obj X)⟩

/-- Finite products in `C` supply an indexed product whenever every indexing type of the fixed
indexing functor is finite.  Nonemptiness is not needed at this general library layer. -/
@[stacks 0B15 "finite indexed-product existence"]
noncomputable instance ofFiniteProducts [HasFiniteProducts C]
    (U : D ⥤ Type w) (V : Dᵒᵖ ⥤ C) [U.ObjFinite] :
    HasIndexedProd U V := ⟨fun _ ↦ inferInstance⟩

/-- Positive powers of `X` supply an indexed product of the constant presheaf at `X` whenever
the indexing functor has nonempty finite values. -/
@[stacks 0182 "constant indexed products from positive powers"]
noncomputable instance (priority := 50) ofPositivePowers
    (U : D ⥤ Type w) (X : C) [HasPositivePowers X]
    [U.ObjFinite] [U.ObjNonempty] :
    HasIndexedProd U ((Functor.const Dᵒᵖ).obj X) :=
  ⟨fun d ↦ HasPositivePowers.hasProductOfFinite X (U.obj d)⟩

namespace Op

/-- A bundled opposite-oriented indexed-product hypothesis supplies its product in every degree. -/
@[stacks 0B15 "degreewise product from opposite indexed-product data"]
instance (priority := 100) hasProductInstance (U : Dᵒᵖ ⥤ Type w) (V : D ⥤ C)
    [HasIndexedProd.Op U V] (d : D) :
    HasProduct (fun _ : U.obj (Opposite.op d) ↦ V.obj d) :=
  HasIndexedProd.Op.hasProduct d

/-- Opposite-oriented fixed indexed products restrict along any functor by precomposition.
The low priority preserves direct owners as the preferred typeclass path. -/
@[stacks 0B15 "restriction of opposite indexed-product existence"]
instance (priority := 40) comp {E : Type j} [Category.{e} E]
    (K : E ⥤ D) (U : Dᵒᵖ ⥤ Type w) (V : D ⥤ C)
    [HasIndexedProd.Op U V] :
    HasIndexedProd.Op (K.op ⋙ U) (K ⋙ V) :=
  ⟨fun X ↦ HasIndexedProd.Op.hasProduct (U := U) (V := V) (K.obj X)⟩

/-- Finite products also supply the covariant orientation of an indexed product whenever its
degreewise indexing types are finite. -/
@[stacks 019V "finite opposite indexed-product existence"]
noncomputable instance ofFiniteProducts [HasFiniteProducts C]
    (U : Dᵒᵖ ⥤ Type w) (V : D ⥤ C) [U.ObjFinite] :
    HasIndexedProd.Op U V := ⟨fun _ ↦ inferInstance⟩

end Op

end HasIndexedProd

namespace HasIndexedProds

/-- A uniform indexed-product hypothesis specializes to every valued presheaf. -/
@[stacks 0B15 "specialization of uniform indexed-product data"]
instance (priority := 100) hasIndexedProdInstance (U : D ⥤ Type w) (C : Type u)
    [Category.{v} C] [HasIndexedProds U C] (V : Dᵒᵖ ⥤ C) : HasIndexedProd U V :=
  HasIndexedProds.hasIndexedProd V

/-- Finite products supply indexed products uniformly for a degreewise finite indexing functor. -/
@[stacks 0B15 "uniform finite indexed-product existence"]
noncomputable instance ofFiniteProducts [HasFiniteProducts C]
    (U : D ⥤ Type w) [U.ObjFinite] : HasIndexedProds U C :=
  ⟨fun V ↦ HasIndexedProd.ofFiniteProducts U V⟩

namespace Op

/-- A uniform opposite-oriented hypothesis specializes to every valued copresheaf. -/
@[stacks 0B15 "specialization of uniform opposite indexed-product data"]
instance (priority := 100) hasIndexedProdInstance (U : Dᵒᵖ ⥤ Type w) (C : Type u)
    [Category.{v} C] [HasIndexedProds.Op U C] (V : D ⥤ C) : HasIndexedProd.Op U V :=
  HasIndexedProds.Op.hasIndexedProd V

/-- Finite products supply opposite-oriented indexed products uniformly for a degreewise finite
indexing functor. -/
@[stacks 0B15 "uniform finite opposite indexed-product existence"]
noncomputable instance ofFiniteProducts [HasFiniteProducts C]
    (U : Dᵒᵖ ⥤ Type w) [U.ObjFinite] : HasIndexedProds.Op U C :=
  ⟨fun V ↦ HasIndexedProd.Op.ofFiniteProducts U V⟩

end Op

end HasIndexedProds

attribute [instance] HasIndexedProds.OfIndex.hasIndexedProds
attribute [instance] HasIndexedProds.Op.OfIndex.hasIndexedProds

namespace HasIndexedProds.OfIndex

/-- Indexed products along the identity indexing functor supply indexed products for every
indexing functor.  This low-priority bridge handles goals where reducing `Functor.id.obj`
erases the indexing functor needed to select the generic projection instance. -/
@[stacks 0B15 "indexed products from the identity indexing functor"]
instance (priority := 40) identity (C : Type u) [Category.{v} C]
    [self : HasIndexedProds.OfIndex (𝟭 (D ⥤ Type w)) C]
    (U : D ⥤ Type w) : HasIndexedProds U C :=
  self.hasIndexedProds U

end HasIndexedProds.OfIndex

namespace HasIndexedProds.Op.OfIndex

/-- Opposite-oriented indexed products along the identity indexing functor supply indexed
products for every presheaf of indices.  This is the variance-symmetric counterpart of
`HasIndexedProds.OfIndex.identity`. -/
@[stacks 0B15 "opposite indexed products from the identity indexing functor"]
instance (priority := 40) identity (C : Type u) [Category.{v} C]
    [self : HasIndexedProds.Op.OfIndex (𝟭 (Dᵒᵖ ⥤ Type w)) C]
    (U : Dᵒᵖ ⥤ Type w) : HasIndexedProds.Op U C :=
  self.hasIndexedProds U

end HasIndexedProds.Op.OfIndex

namespace HasIndexedPowers

/-- A fixed-valued indexed-power owner specializes to every covariant indexing functor. -/
@[stacks 0B15 "specialization of fixed-presheaf indexed powers"]
instance (priority := 50) hasIndexedProdInstance (V : Dᵒᵖ ⥤ C)
    [self : HasIndexedPowers.{i, w, d, v, u} V]
    (U : D ⥤ Type w) : HasIndexedProd U V :=
  self.hasIndexedProd U

/-- A category with all products supplies indexed powers of every fixed valued presheaf. -/
@[stacks 0B15 "fixed-presheaf indexed powers from products"]
instance ofProducts [HasProducts.{w} C] (V : Dᵒᵖ ⥤ C) :
    HasIndexedPowers.{i, w, d, v, u} V :=
  ⟨fun _ ↦ ⟨fun _ ↦ inferInstance⟩⟩

namespace Op

/-- A fixed-valued opposite indexed-power owner specializes to every presheaf of indices. -/
@[stacks 0B15 "specialization of fixed-copresheaf opposite indexed powers"]
instance (priority := 50) hasIndexedProdInstance (V : D ⥤ C)
    [self : HasIndexedPowers.Op.{i, w, d, v, u} V]
    (U : Dᵒᵖ ⥤ Type w) : HasIndexedProd.Op U V :=
  self.hasIndexedProd U

/-- A category with all products supplies opposite-oriented indexed powers of every valued
copresheaf. -/
@[stacks 0B15 "fixed-copresheaf opposite indexed powers from products"]
instance ofProducts [HasProducts.{w} C] (V : D ⥤ C) :
    HasIndexedPowers.Op.{i, w, d, v, u} V :=
  ⟨fun _ ↦ ⟨fun _ ↦ inferInstance⟩⟩

end Op

end HasIndexedPowers

end CategoryTheory.Functor
