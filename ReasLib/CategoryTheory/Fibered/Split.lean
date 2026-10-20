/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Cleavage.Basic.Reindex.Functor
public import Mathlib.CategoryTheory.Category.Cat
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Opposite

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

namespace Functor.Cleavage

variable {p : S ⥤ C}

/-- A cleavage is split when its chosen reindexing objects and chosen strongly cartesian arrows
are strictly closed under identities and composition. The arrow laws explicitly transport along
the preceding object equalities, so they compare ordinary morphisms rather than hiding the source
alignment in `HEq`. Strict functoriality of reindexing is derived from these lift-level laws. -/
@[stacks 02XW "intrinsic split cleavage"]
structure IsSplit (χ : p.Cleavage) : Prop where
  /-- The chosen reindexing object over an identity is the original fiber object. -/
  reindexObj_id (U : C) (x : p.Fiber U) :
    χ.reindexObj (𝟙 U) x = x
  /-- After aligning its source by `reindexObj_id`, the chosen cartesian arrow over an identity is
  the identity arrow. -/
  cartesianHom_id (U : C) (x : p.Fiber U) :
    eqToHom (congrArg Subtype.val (reindexObj_id U x)).symm ≫
        χ.cartesianHom (𝟙 U) x =
      𝟙 x.1
  /-- The chosen reindexing object over a composite is obtained by the two successive chosen
  reindexings. -/
  reindexObj_comp ⦃U V W : C⦄ (f : V ⟶ U) (g : W ⟶ V) (x : p.Fiber U) :
    χ.reindexObj (g ≫ f) x =
      χ.reindexObj g (χ.reindexObj f x)
  /-- After aligning its source by `reindexObj_comp`, the chosen cartesian arrow over a composite
  is the composite of the two chosen cartesian arrows. -/
  cartesianHom_comp ⦃U V W : C⦄ (f : V ⟶ U) (g : W ⟶ V) (x : p.Fiber U) :
    eqToHom (congrArg Subtype.val (reindexObj_comp f g x)).symm ≫
        χ.cartesianHom (g ≫ f) x =
      χ.cartesianHom g (χ.reindexObj f x) ≫ χ.cartesianHom f x

/-- The four strict identity and composition laws carried by a split cleavage, exposed together
for source-facing destructuring. The arrow equalities use the object equalities stored in the
same witness, so no heterogeneous equality or additional transport choice enters the API. -/
@[stacks 02XW "split cleavage laws"]
theorem IsSplit.spec {χ : p.Cleavage} (hχ : χ.IsSplit) :
    (∀ (U : C) (x : p.Fiber U), χ.reindexObj (𝟙 U) x = x) ∧
    (∀ (U : C) (x : p.Fiber U),
      eqToHom (congrArg Subtype.val (hχ.reindexObj_id U x)).symm ≫
          χ.cartesianHom (𝟙 U) x =
        𝟙 x.1) ∧
    (∀ ⦃U V W : C⦄ (f : V ⟶ U) (g : W ⟶ V) (x : p.Fiber U),
      χ.reindexObj (g ≫ f) x = χ.reindexObj g (χ.reindexObj f x)) ∧
    (∀ ⦃U V W : C⦄ (f : V ⟶ U) (g : W ⟶ V) (x : p.Fiber U),
      eqToHom (congrArg Subtype.val (hχ.reindexObj_comp f g x)).symm ≫
          χ.cartesianHom (g ≫ f) x =
        χ.cartesianHom g (χ.reindexObj f x) ≫ χ.cartesianHom f x) := sorry

/-- Reindexing along an identity is literally the identity functor for a split cleavage. -/
theorem IsSplit.map_id {χ : p.Cleavage} (hχ : χ.IsSplit) (U : C) :
    (𝟙 U)⁎[χ] = 𝟭 (p.Fiber U) := sorry
/- Proof strategy: apply `Functor.ext` with object components `hχ.reindexObj_id U`; use
`Cleavage.reindexMap.fac`, `hχ.cartesianHom_id`, and cartesian-arrow uniqueness to identify the
transported morphism actions. -/

/-- Reindexing along a composite is literally the composite of the two reindexing functors for a
split cleavage. -/
theorem IsSplit.map_comp {χ : p.Cleavage} (hχ : χ.IsSplit)
    ⦃U V W : C⦄ (f : V ⟶ U) (g : W ⟶ V) :
    (g ≫ f)⁎[χ] = f⁎[χ] ⋙ g⁎[χ] := sorry
/- Proof strategy: apply `Functor.ext` with object components `hχ.reindexObj_comp f g`; use
`Cleavage.reindexMap.fac` twice, `hχ.cartesianHom_comp`, and cartesian-arrow uniqueness for the
transported morphism actions. -/

/-- A cleavage has strictly compositional reindexing when the reindexing functor of every
composite is literally the composite of the two reindexing functors.

This is exactly the pullback-choice condition in Stacks, Lemma 4.36.3 (02XX).  It deliberately
contains no identity-lift or chosen-cartesian-arrow condition: those belong to
`Cleavage.IsSplit`. It does not by itself normalize a cleavage to `Cleavage.IsSplit` or produce
a `Functor.IsFibered.Split` witness; that requires additional strict chosen-arrow laws. -/
@[stacks 02XX "strictly compositional pullback choice"]
def IsStrictlyCompositional (χ : p.Cleavage) : Prop :=
  ∀ ⦃U V W : C⦄ (f : V ⟶ U) (g : W ⟶ V),
    (g ≫ f)⁎[χ] = f⁎[χ] ⋙ g⁎[χ]

/-- The reindexing functors of a split cleavage are strictly compositional. -/
theorem IsSplit.isStrictlyCompositional {χ : p.Cleavage} (hχ : χ.IsSplit) :
    χ.IsStrictlyCompositional := sorry

end Functor.Cleavage

namespace Functor

/-- A splitting of `p : S ⥤ C`: chosen strongly cartesian lifts whose source objects and arrows
are strictly the identity lifts and composites of the previously chosen lifts.

This is the intrinsic data owner. Co-Grothendieck presentations and pseudofunctors are semantic
models derived from it, while strict functoriality of reindexing is a theorem rather than the
primitive splitting datum. -/
@[stacks 02XW "split cleavage data"]
structure SplitCleavage (p : S ⥤ C) where
  /-- The underlying choice of strongly cartesian lifts. -/
  toCleavage : p.Cleavage
  /-- The chosen lift objects and arrows are strictly closed under identities and composition. -/
  isSplit : toCleavage.IsSplit

namespace SplitCleavage

variable {p : S ⥤ C}

/-- A split cleavage can be used wherever an ordinary cleavage is expected. -/
instance : CoeOut p.SplitCleavage p.Cleavage where
  coe χ := χ.toCleavage

/-- A split cleavage exhibits its projection as a fibred category. -/
theorem isFibered (χ : p.SplitCleavage) : p.IsFibered := sorry
/- Proof strategy: apply `Functor.Cleavage.isFibered χ.toCleavage`. -/

/-- The strict contravariant `Cat`-valued presheaf determined by explicit split-cleavage data.

Its values are the standard fibers of `p`; its restriction along `f` is the chosen reindexing
functor. The strict identity and composition fields are exactly `χ.isSplit.map_id` and
`χ.isSplit.map_comp`, so this construction preserves the chosen data without invoking a
noncanonical choice from `Functor.IsFibered.Split`. -/
@[stacks 02XW "strict fiber presheaf from split cleavage"]
noncomputable def toCatPresheaf (χ : p.SplitCleavage) : Cᵒᵖ ⥤ Cat.{v₂, u₂} where
  obj U := Cat.of (p.Fiber U.unop)
  map f := ((f.unop)⁎[χ.toCleavage]).toCatHom
  map_id U := congrArg Functor.toCatHom (χ.isSplit.map_id U.unop)
  map_comp f g := congrArg Functor.toCatHom (χ.isSplit.map_comp f.unop g.unop)

/-- The value of the strict fiber presheaf at `U` is the standard fiber over `U`. -/
@[simp]
theorem toCatPresheaf_obj (χ : p.SplitCleavage) (U : C) :
    χ.toCatPresheaf.obj (Opposite.op U) = Cat.of (p.Fiber U) := sorry

/-- The strict fiber presheaf restricts along `f` by the reindexing functor selected by its
split cleavage. -/
@[simp]
theorem toCatPresheaf_map (χ : p.SplitCleavage) {U V : C} (f : V ⟶ U) :
    (χ.toCatPresheaf.map f.op).toFunctor = χ.toCleavage.reindex f := sorry

end SplitCleavage

/-- A functor is split fibred when it admits chosen strongly cartesian lifts that themselves are
strictly closed under identity and composition. -/
@[stacks 02XW]
class IsFibered.Split (p : S ⥤ C) : Prop where
  /-- Existence of a cleavage satisfying the strict lift-level identity and composition laws. -/
  exists_splitCleavage : Nonempty p.SplitCleavage

namespace IsFibered.Split

/-- A split fibred category is fibred over its base. -/
theorem isFibered {p : S ⥤ C} (hp : IsFibered.Split p) : p.IsFibered := sorry
/- Proof strategy: choose `χ` from `hp.exists_splitCleavage` and apply `χ.isFibered`. -/

/-- A functor is split fibred if and only if it admits a cleavage whose chosen lift objects and
chosen cartesian arrows are strictly unital and compositional.

This is the complete formal strict-lift criterion.  Equality of reindexing functors alone is
weaker because it forgets the selected cartesian arrows; it is therefore exposed separately by
`Cleavage.IsStrictlyCompositional` and only used in the forward direction below. -/
@[stacks 02XX "formal strict-lift criterion"]
theorem iff_existsCleavageIsSplit (p : S ⥤ C) :
    IsFibered.Split p ↔ ∃ χ : p.Cleavage, χ.IsSplit := sorry

/-- A splitting supplies a cleavage with strictly compositional reindexing functors.

This is the sound pullback-functor consequence appearing in Stacks, Lemma 4.36.3 (02XX).
The converse is intentionally absent: reindexing-functor equalities do not determine the chosen
cartesian arrows of a cleavage. -/
@[stacks 02XX "forward pullback-functor consequence"]
theorem existsCleavageReindexComp
    {p : S ⥤ C} (hp : IsFibered.Split p) :
    ∃ χ : p.Cleavage, χ.IsStrictlyCompositional := sorry

/-- A cleavage satisfying the complete strict lift laws determines a splitting. -/
theorem ofCleavageIsSplit
    {p : S ⥤ C} {χ : p.Cleavage} (hχ : χ.IsSplit) :
    IsFibered.Split p := sorry

end IsFibered.Split

/-- Fibredness induced by an intrinsic splitting is available to typeclass search. -/
instance (p : S ⥤ C) [IsFibered.Split p] : p.IsFibered := sorry
/- Proof strategy: apply `IsFibered.Split.isFibered inferInstance`. -/

end Functor
end CategoryTheory
