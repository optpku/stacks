module

public import Mathlib.CategoryTheory.Action.Concrete

/-!
# Coinduced maps of actions

This module records the underlying set-level part of coinduction along a monoid homomorphism.
The bundled `Action`-level functor can be built on top of this owner without making its induced
action an ambient instance.
-/

@[expose] public section

universe u v

namespace CategoryTheory

namespace Action

/-- The left `G`-action on `H` obtained by restricting along `φ : G →* H`.

This is named data rather than a global instance because a raw type `H` can carry other
mathematically relevant `G`-actions. -/
@[reducible]
def restrictionDomainMulAction {G H : Type u} [Monoid G] [Monoid H] (φ : G →* H) :
    MulAction G H :=
  MulAction.compHom H φ

/-- Maps from `H` to a `G`-action `S` equivariant for the left `G`-action on `H` induced by
`φ : G →* H`.

The action equation is expressed using bundled action maps, so this object carries no hidden
ambient action instance on `H`. -/
structure CoinducedMap {G H : Type u} [Monoid G] [Monoid H] (φ : G →* H)
    (S : Action (Type v) G) where
  /-- The underlying function on `H`. -/
  toFun : H → S.V
  /-- Equivariance for the action of `G` on `H` induced by `φ`. -/
  map_action : ∀ (g : G) (h : H), toFun (φ g * h) = S.ρ g (toFun h)

/-- Coinduced maps are used as functions on `H`. -/
instance coinducedMapCoeFun {G H : Type u} [Monoid G] [Monoid H] (φ : G →* H)
    (S : Action (Type v) G) : CoeFun (CoinducedMap φ S) (fun _ ↦ H → S.V) where
  coe := CoinducedMap.toFun

/-- Coinduced maps are equal when their underlying functions agree. -/
@[ext]
theorem CoinducedMap.ext {G H : Type u} [Monoid G] [Monoid H] {φ : G →* H}
    {S : Action (Type v) G} {a b : CoinducedMap φ S}
    (h : ∀ x : H, a.toFun x = b.toFun x) : a = b := sorry

/-- Right translation of a coinduced equivariant map. -/
def coinducedRightTranslation {G H : Type u} [Monoid G] [Monoid H] (φ : G →* H)
    (S : Action (Type v) G) (h : H) : CoinducedMap φ S → CoinducedMap φ S :=
  fun a ↦
    { toFun := fun x ↦ a.toFun (x * h)
      map_action := sorry }

/-- The named right-translation action of `H` on coinduced maps.

It is deliberately not a global instance, since the same raw carrier can support other actions
in downstream developments. -/
@[reducible]
def coinducedRightTranslationMulAction {G H : Type u} [Monoid G] [Monoid H] (φ : G →* H)
    (S : Action (Type v) G) : MulAction H (CoinducedMap φ S) where
  smul h := coinducedRightTranslation φ S h
  one_smul := sorry
  mul_smul := sorry

/-- The `H`-action coinduced from a `G`-action along `φ`, with right translation on maps. -/
def coinducedAction {G H : Type u} [Monoid G] [Monoid H] (φ : G →* H)
    (S : Action (Type v) G) : Action (Type (max u v)) H :=
  @Action.ofMulAction H (CoinducedMap φ S) _ (coinducedRightTranslationMulAction φ S)

/-- The action on coinduced maps is precomposition by right multiplication. -/
@[simp]
theorem coinducedAction_rho_apply {G H : Type u} [Monoid G] [Monoid H] (φ : G →* H)
    (S : Action (Type v) G) (h x : H) (a : CoinducedMap φ S) :
    ((coinducedAction φ S).ρ h a).toFun x = a.toFun (x * h) := sorry

/-- Evaluation at the identity of `H` on maps coinduced along `φ`. -/
def coinducedEvalOne {G H : Type u} [Monoid G] [Monoid H] (φ : G →* H)
    (S : Action (Type v) G) : CoinducedMap φ S → S.V :=
  fun a ↦ a.toFun 1

/-- The coinduced evaluation map is application at the identity. -/
theorem coinducedEvalOne_apply {G H : Type u} [Monoid G] [Monoid H] (φ : G →* H)
    (S : Action (Type v) G) (a : CoinducedMap φ S) :
    coinducedEvalOne φ S a = a.toFun 1 := sorry

/-- Evaluation at `1` is surjective on coinduced maps when `φ` is injective. -/
theorem coinducedEvalOne_surjective_of_injective
    {G H : Type u} [Group G] [Group H] (φ : G →* H) (hφ : Function.Injective φ)
    (S : Action (Type v) G) :
    Function.Surjective (coinducedEvalOne φ S) := sorry

end Action

end CategoryTheory
