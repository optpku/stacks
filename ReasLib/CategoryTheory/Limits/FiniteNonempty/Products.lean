module

public import ReasLib.CategoryTheory.Limits.FiniteNonempty.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.Logic.Unique
import Mathlib.Tactic.CrossRefAttribute

/-!
# Products indexed by finite nonempty types

This leaf constructs products and coproducts indexed by arbitrary finite nonempty types from
binary products and coproducts.  The positive finite ordinal constructions are exposed separately
so objectwise power APIs can import this layer without importing finite-limit criteria.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.Limits

open CategoryTheory

variable (C : Type u) [Category.{v} C]

namespace FiniteNonempty

/-- Extend a chosen product cone for the tail of a positive finite family by one binary
product. -/
@[stacks 04AU "extend a positive finite product cone"]
noncomputable def extendProductCone [HasBinaryProducts C] {n : ℕ}
    (f : Fin (n + 1) → C)
    (tail : LimitCone (Discrete.functor fun i : Fin n ↦ f i.succ)) :
    LimitCone (Discrete.functor f) :=
  ⟨CategoryTheory.extendFan tail.cone
      (getLimitCone (pair (f 0) tail.cone.pt)).cone,
    CategoryTheory.extendFanIsLimit f tail.isLimit
      (getLimitCone (pair (f 0) tail.cone.pt)).isLimit⟩

/-- A chosen product cone for a positive finite family, built recursively from binary products.
The singleton case is the family member itself, so no terminal object is required. -/
@[stacks 04AU "positive finite products from binary products"]
noncomputable def productCone [HasBinaryProducts C] :
    ∀ (n : ℕ) (f : Fin (n + 1) → C), LimitCone (Discrete.functor f)
  | 0, f => @limitConeOfUnique _ _ _ Fin.instUnique f
  | n + 1, f =>
      extendProductCone C f (productCone n (fun i ↦ f i.succ))

/-- Binary products explicitly supply a product for every positive finite family. -/
@[implicit_reducible, stacks 04AU "positive finite product existence"]
noncomputable def hasProductFinSucc [HasBinaryProducts C]
    (n : ℕ) (f : Fin (n + 1) → C) : HasProduct f :=
  HasLimit.mk (productCone C n f)

/-- Extend a chosen coproduct cocone for the tail of a positive finite family by one binary
coproduct. -/
@[stacks 04AW "extend a positive finite coproduct cocone"]
noncomputable def extendCoproductCocone [HasBinaryCoproducts C] {n : ℕ}
    (f : Fin (n + 1) → C)
    (tail : ColimitCocone (Discrete.functor fun i : Fin n ↦ f i.succ)) :
    ColimitCocone (Discrete.functor f) :=
  ⟨CategoryTheory.extendCofan tail.cocone
      (getColimitCocone (pair (f 0) tail.cocone.pt)).cocone,
    CategoryTheory.extendCofanIsColimit f tail.isColimit
      (getColimitCocone (pair (f 0) tail.cocone.pt)).isColimit⟩

/-- A chosen coproduct cocone for a positive finite family, built recursively from binary
coproducts. The singleton case is the family member itself, so no initial object is required. -/
@[stacks 04AW "positive finite coproducts from binary coproducts"]
noncomputable def coproductCocone [HasBinaryCoproducts C] :
    ∀ (n : ℕ) (f : Fin (n + 1) → C), ColimitCocone (Discrete.functor f)
  | 0, f => @colimitCoconeOfUnique _ _ _ Fin.instUnique f
  | n + 1, f =>
      extendCoproductCocone C f (coproductCocone n (fun i ↦ f i.succ))

/-- Binary coproducts explicitly supply a coproduct for every positive finite family. -/
@[implicit_reducible, stacks 04AW "positive finite coproduct existence"]
noncomputable def hasCoproductFinSucc [HasBinaryCoproducts C]
    (n : ℕ) (f : Fin (n + 1) → C) : HasCoproduct f :=
  HasColimit.mk (coproductCocone C n f)

end FiniteNonempty

/-- Transport a chosen positive finite product along an explicit finite indexing equivalence.
The impossible empty-index case is discharged using the nonemptiness of the source type. -/
@[implicit_reducible, stacks 04AU "positive finite products under reindexing"]
noncomputable def productOfEquiv {ι : Type w} [Nonempty ι]
    [HasBinaryProducts C] (f : ι → C) :
    (n : ℕ) → (ι ≃ Fin n) → HasProduct f
  | 0, e =>
      Nonempty.elim (inferInstance : Nonempty ι) (fun i ↦ Fin.elim0 (e i))
  | n + 1, e =>
      @hasProduct_of_equiv_of_iso
        ι (Fin (n + 1)) C _ (fun j ↦ f (e.symm j)) f
        (FiniteNonempty.hasProductFinSucc C n (fun j ↦ f (e.symm j))) e
        (fun i ↦ eqToIso (congrArg f (e.symm_apply_apply i).symm))

/-- Transport a chosen positive finite coproduct along an explicit finite indexing equivalence.
The impossible empty-index case is discharged using the nonemptiness of the source type. -/
@[implicit_reducible, stacks 04AW "positive finite coproducts under reindexing"]
noncomputable def coproductOfEquiv {ι : Type w} [Nonempty ι]
    [HasBinaryCoproducts C] (f : ι → C) :
    (n : ℕ) → (ι ≃ Fin n) → HasCoproduct f
  | 0, e =>
      Nonempty.elim (inferInstance : Nonempty ι) (fun i ↦ Fin.elim0 (e i))
  | n + 1, e =>
      @hasCoproduct_of_equiv_of_iso
        ι (Fin (n + 1)) C _ (fun j ↦ f (e.symm j)) f
        (FiniteNonempty.hasCoproductFinSucc C n (fun j ↦ f (e.symm j))) e
        (fun i ↦ eqToIso (congrArg f (e.symm_apply_apply i).symm))

/-- Binary products give products indexed by any finite nonempty type. -/
@[implicit_reducible, stacks 04AU "products indexed by finite nonempty types"]
noncomputable def hasProduct_of_finite_of_nonempty {ι : Type w}
    [Finite ι] [Nonempty ι] [HasBinaryProducts C] (f : ι → C) : HasProduct f :=
  Exists.elim (Finite.exists_equiv_fin ι) fun n e ↦
    Nonempty.elim e fun indexEquiv ↦ productOfEquiv C f n indexEquiv

/-- Binary coproducts give coproducts indexed by any finite nonempty type. -/
@[implicit_reducible, stacks 04AW "coproducts indexed by finite nonempty types"]
noncomputable def hasCoproduct_of_finite_of_nonempty {ι : Type w}
    [Finite ι] [Nonempty ι] [HasBinaryCoproducts C] (f : ι → C) : HasCoproduct f :=
  Exists.elim (Finite.exists_equiv_fin ι) fun n e ↦
    Nonempty.elim e fun indexEquiv ↦ coproductOfEquiv C f n indexEquiv

end CategoryTheory.Limits
