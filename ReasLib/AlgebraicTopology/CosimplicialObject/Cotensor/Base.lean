/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import ReasLib.AlgebraicTopology.SimplicialSet.Objwise
public import ReasLib.CategoryTheory.Functor.IndexedProduct.Op.HomFamily
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 019V

# Simplicial-set cotensors of cosimplicial objects

This file owns the existence predicates, degreewise cotensor, its structure maps, and the
universal extensionality API for maps into it.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section

universe w v u e d

namespace CategoryTheory.CosimplicialObject

variable {C : Type u} [Category.{v} C]

/-- `HasCotensor U V` records exactly the degreewise products used by the cotensor of the
fixed cosimplicial object `V` by the fixed simplicial set `U`. -/
@[stacks 019V "fixed-object cosimplicial cotensor"]
abbrev HasCotensor (U : SSet.{w}) (V : CosimplicialObject C) : Prop :=
  Functor.HasIndexedProd.Op U V

/-- `V.HasCotensorsOf` records that the fixed cosimplicial object `V` can be cotensored by
every simplicial set. It is the fixed-object counterpart of `HasCotensors U C`. -/
@[stacks 019V "fixed-object cosimplicial cotensors"]
abbrev HasCotensorsOf (V : CosimplicialObject C) : Prop :=
  Functor.HasIndexedPowers.Op.{0, w, 0, v, u} V

/-- `HasCotensors U C` says that cotensoring by `U` is defined for every cosimplicial
object in `C`. -/
@[stacks 019V "fixed-index cosimplicial cotensors"]
abbrev HasCotensors (U : SSet.{w}) (C : Type u) [Category.{v} C] : Prop :=
  Functor.HasIndexedProds.Op U C

namespace HasCotensors

/-- A category with all `w`-small products admits cotensors by every `w`-small simplicial set. -/
@[stacks 019V "cosimplicial cotensors from products"]
instance ofProducts [HasProducts.{w} C] (U : SSet.{w}) : HasCotensors U C := sorry

end HasCotensors

/-- `HasCotensors.OfIndex K C` records cotensors by every simplicial set in the image of `K`,
uniformly in the cosimplicial object. -/
@[stacks 019V "cotensors along an indexing functor"]
abbrev HasCotensors.OfIndex {D : Type d} [Category.{e} D]
    (K : D ⥤ SSet.{w}) (C : Type u) [Category.{v} C] : Prop :=
  Functor.HasIndexedProds.Op.OfIndex K C

namespace HasCotensors.OfIndex

/-- Categories with all `w`-small products admit cotensors along every simplicial indexing
functor. -/
@[stacks 019V "indexed cosimplicial cotensors from products"]
instance ofProducts {D : Type d} [Category.{e} D] [HasProducts.{w} C]
    (K : D ⥤ SSet.{w}) : HasCotensors.OfIndex K C := sorry

end HasCotensors.OfIndex

section Cotensor

variable (U : SSet.{w}) (V : CosimplicialObject C)
variable [HasCotensor U V]

/-- The cotensor of a cosimplicial object `V` by a simplicial set `U`. Its value at `n` is
the product of `U.obj (op n)` copies of `V.obj n`. -/
@[stacks 019V]
abbrev cotensor : CosimplicialObject C := Functor.indexedProd.op U V

/-- The degreewise cotensor object is the corresponding indexed product. -/
@[simp, stacks 019V "cotensor object computation"]
theorem cotensor.obj (n : SimplexCategory) :
    (cotensor U V).obj n = ∏ᶜ (fun _ : U.obj (op n) ↦ V.obj n) := sorry

/-- The cotensor structure map is the reindexing map between the corresponding products. -/
@[simp, stacks 019V "cotensor map computation"]
theorem cotensor.map {m n : SimplexCategory} (f : m ⟶ n) :
    (cotensor U V).map f = Pi.map' (U.map f.op) (fun _ ↦ V.map f) := sorry

/-- The structure map of `cotensor U V` commutes with every product projection. -/
@[stacks 019V "cotensor projection square"]
theorem cotensor.map.π {m n : SimplexCategory} (f : m ⟶ n) (u : U.obj (op n)) :
    CommSq
      ((cotensor U V).map f)
      (Pi.π (fun _ : U.obj (op m) ↦ V.obj m) (U.map f.op u))
      (Pi.π (fun _ : U.obj (op n) ↦ V.obj n) u)
      (V.map f) := sorry

/-- A morphism into a cotensor is componentwise natural after evaluation at any index. -/
@[stacks 019V "cotensor morphism naturality"]
theorem cotensor.hom.naturality {X : CosimplicialObject C}
    (h : X ⟶ cotensor U V) {m n : SimplexCategory} (f : m ⟶ n)
    (u : U.obj (op n)) :
    CommSq
      (X.map f)
      (h.app m ≫ Pi.π (fun _ : U.obj (op m) ↦ V.obj m) (U.map f.op u))
      (h.app n ≫ Pi.π (fun _ : U.obj (op n) ↦ V.obj n) u)
      (V.map f) := sorry

/-- A morphism into a cotensor is determined by all of its degreewise product projections. -/
@[ext, stacks 019V "cotensor morphism extensionality"]
theorem cotensor.hom_ext {X : CosimplicialObject C} {f g : X ⟶ cotensor U V}
    (h : ∀ (n : SimplexCategory) (u : U.obj (op n)),
      f.app n ≫ Pi.π (fun _ : U.obj (op n) ↦ V.obj n) u =
        g.app n ≫ Pi.π (fun _ : U.obj (op n) ↦ V.obj n) u) :
    f = g := sorry

end Cotensor

end CategoryTheory.CosimplicialObject
