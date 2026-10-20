/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import ReasLib.CategoryTheory.Functor.IndexedCoproduct
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 017C

# Simplicial-set-indexed copower

Given a simplicial set `U : SSet` and a simplicial object `V : SimplicialObject C` in a
category with sufficient coproducts, the **copower** `SimplicialObject.copower U V` is the
simplicial object whose value at `Δ` is the coproduct of `U.obj Δ` copies of `V.obj Δ`,
with structure maps induced by `U` and `V`.

This includes both the full simplicial version and the truncated variant.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

/-- `HasCopower U X` records the degreewise coproducts needed for one fixed simplicial object
`X : SimplicialObject C` to form `copower U X`. -/
@[stacks 017C "fixed-object simplicial copower"]
abbrev HasCopower (U : SSet.{w}) (X : SimplicialObject C) : Prop :=
  Functor.HasIndexedCoprod U X

/-- `X.HasCopowersOf` records that the fixed simplicial object `X` can be copowered by every
simplicial set. It is the fixed-object counterpart of `HasCopowers U C`. -/
@[stacks 017C "fixed-object simplicial copowers"]
abbrev HasCopowersOf (X : SimplicialObject C) : Prop :=
  Functor.HasIndexedCopowers.{w} X

/-- `HasCopowers U C` says that the degreewise coproducts defining `copower U X` exist for
every simplicial object `X : SimplicialObject C`.  It is the fixed-index existence interface
used by functorial copowers and simplicial internal homs. -/
@[stacks 017C "fixed-index simplicial copowers"]
abbrev HasCopowers (U : SSet.{w}) (C : Type u) [Category.{v} C] : Prop :=
  Functor.HasIndexedCoprods U C

namespace HasCopowers

/-- A category with all `w`-small coproducts admits copowers by every `w`-small
simplicial set. -/
@[stacks 017C "simplicial copowers from coproducts"]
instance ofCoproducts [HasCoproducts.{w} C] (U : SSet.{w}) : HasCopowers U C :=
  ⟨fun _ ↦ ⟨fun _ ↦ inferInstance⟩⟩

end HasCopowers

/-- `HasConstCopowers U C` records only the copowers of `U` by constant simplicial objects.
This is the exact existence interface for constant-factor tensor-hom constructions; it is weaker
than `HasCopowers U C`, which also asks for arbitrary simplicial objects. -/
@[stacks 017C "constant-factor simplicial copowers"]
class HasConstCopowers (U : SSet.{w}) (C : Type u) [Category.{v} C] : Prop where
  /-- The copower by the constant simplicial object on `X`. -/
  hasCopower (X : C) : HasCopower U ((const C).obj X)

namespace HasConstCopowers

/-- A constant-copower owner supplies the corresponding fixed-object copower instance. -/
@[stacks 017C "constant copower instance"]
instance (priority := 90) hasCopowerInstance (U : SSet.{w}) (C : Type u)
    [Category.{v} C] [HasConstCopowers U C] (X : C) : HasCopower U ((const C).obj X) :=
  HasConstCopowers.hasCopower X

/-- Copowers by all simplicial objects in particular supply copowers by constant objects. -/
@[stacks 017C "constant copowers from simplicial copowers"]
instance ofHasCopowers (U : SSet.{w}) (C : Type u) [Category.{v} C] [HasCopowers U C] :
    HasConstCopowers U C :=
  ⟨fun X ↦ Functor.HasIndexedCoprods.hasIndexedCoprod ((const C).obj X)⟩

end HasConstCopowers

variable (U : SSet.{w}) (V : SimplicialObject C)
variable [HasCopower U V]

/-- The copower of a simplicial object `V` by a simplicial set `U`. Its value at `Δ` is
`∐ (fun _ : U.obj Δ ↦ V.obj Δ)`, with structure maps given by reindexing via `U` and
postcomposing via `V`. -/
@[stacks 017C]
abbrev copower : SimplicialObject C := Functor.indexedCoprod U V

/-- The value of a simplicial copower is the coproduct indexed by the simplices in that degree. -/
@[simp, stacks 017C "copower object formula"] theorem copower.obj (Δ : SimplexCategoryᵒᵖ) :
    (copower U V).obj Δ = ∐ (fun _ : U.obj Δ ↦ V.obj Δ) :=
  sorry

/-- A copower structure map reindexes summands and applies the simplicial-object structure map. -/
@[simp, stacks 017C "copower map formula"]
theorem copower.map {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') :
    (copower U V).map f = Sigma.map' (U.map f) (fun _ ↦ V.map f) :=
  sorry

end CategoryTheory.SimplicialObject

namespace CategoryTheory.SimplicialObject.Truncated

variable {C : Type u} [Category.{v} C]
variable {n : ℕ}

/-- `Truncated.HasCopower U X` records the degreewise coproducts needed for one fixed
truncated simplicial object `X` to form `Truncated.copower U X`. -/
@[stacks 017C "fixed-object truncated simplicial copower"]
abbrev HasCopower (U : SSet.Truncated.{w} n) (X : SimplicialObject.Truncated C n) : Prop :=
  Functor.HasIndexedCoprod U X

/-- `X.HasCopowersOf` records that the fixed truncated simplicial object `X` can be copowered by
every truncated simplicial set. -/
@[stacks 017C "fixed-object truncated simplicial copowers"]
abbrev HasCopowersOf (X : SimplicialObject.Truncated C n) : Prop :=
  Functor.HasIndexedCopowers.{w} X

/-- `Truncated.HasCopowers U C` says that the degreewise coproducts defining
`Truncated.copower U X` exist for every truncated simplicial object `X`. -/
@[stacks 017C "fixed-index truncated simplicial copowers"]
abbrev HasCopowers (U : SSet.Truncated.{w} n) (C : Type u) [Category.{v} C] : Prop :=
  Functor.HasIndexedCoprods U C

namespace HasCopowers

/-- A category with all `w`-small coproducts admits truncated copowers by every
`w`-small truncated simplicial set. -/
@[stacks 017C "truncated simplicial copowers from coproducts"]
instance ofCoproducts [HasCoproducts.{w} C] (U : SSet.Truncated.{w} n) :
    HasCopowers U C :=
  ⟨fun _ ↦ ⟨fun _ ↦ inferInstance⟩⟩

end HasCopowers

variable (U : SSet.Truncated n) (V : SimplicialObject.Truncated C n)
variable [HasCopower U V]

/-- The truncated copower of a truncated simplicial object `V` by a truncated simplicial
set `U`. -/
@[stacks 017C "truncated simplicial copower"]
abbrev copower : SimplicialObject.Truncated C n := Functor.indexedCoprod U V

/-- The value of a truncated copower is the degreewise coproduct over its indexing simplices. -/
@[simp, stacks 017C "truncated copower object formula"]
theorem copower.obj (Δ : (SimplexCategory.Truncated n)ᵒᵖ) :
    (copower U V).obj Δ = ∐ (fun _ : U.obj Δ ↦ V.obj Δ) :=
  sorry

/-- A truncated copower structure map reindexes summands and applies the valued structure map. -/
@[simp, stacks 017C "truncated copower map formula"]
theorem copower.map {Δ Δ' : (SimplexCategory.Truncated n)ᵒᵖ} (f : Δ ⟶ Δ') :
    (copower U V).map f = Sigma.map' (U.map f) (fun _ ↦ V.map f) :=
  sorry

end CategoryTheory.SimplicialObject.Truncated
