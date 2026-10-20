/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.Gysin
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily.Operations

/-!
# Cycle-level actions of relative cycles

This file records cartesian-square-indexed operations on cycle groups, compatible with
proper pushforward, flat pullback, and trivial-restriction Gysin, together with the
action associated to a relative cycle.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme (Modules)
open AlgebraicGeometry.Scheme.Modules hiding pullback
open AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- The cartesian-square-indexed cap maps underlying a cycle-level action of relative
degree `r` for `f : X ⟶ Y`. -/
abbrev CapFamily
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [LocallyOfFiniteType f.left] (r : ℕ) :=
  ∀ {X' Y' : Over S} [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y) [LocallyOfFiniteType g.left],
    IsPullback i.left f'.left f.left g.left → ∀ e : ℤ,
      CycleGroup Y'.left (Y'.hom.relativeDimensionFunction δ) e →+
        CycleGroup X'.left
          ((f'.left ≫ Y'.hom).relativeDimensionFunction δ) ((r : ℤ) + e)

/-- Compatibility of cycle-level cap maps with proper pushforward in a cartesian
square. -/
def CompatibleWithProperPushforward
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    {f : X ⟶ Y} [LocallyOfFiniteType f.left] {r : ℕ} (cap : CapFamily δ f r) :
    Prop :=
  ∀ {X' Y' X'' Y'' : Over S}
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    [LocallyOfFiniteType X''.hom] [LocallyOfFiniteType Y''.hom]
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y) [LocallyOfFiniteType g.left]
    (outer : IsPullback i.left f'.left f.left g.left)
    (j : X'' ⟶ X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ Y')
    (inner : IsPullback j.left f''.left f'.left h.left)
    [IsProper h.left] [IsProper j.left] (e : ℤ)
    (β'' : CycleGroup Y''.left (Y''.hom.relativeDimensionFunction δ) e),
    cap i f' g outer e
        (CycleGroup.mapHom h.left (Y''.hom.relativeDimensionFunction δ)
          (Y'.hom.relativeDimensionFunction δ) e β'') =
      CycleGroup.mapHom j.left
        ((f''.left ≫ Y''.hom).relativeDimensionFunction δ)
        ((f'.left ≫ Y'.hom).relativeDimensionFunction δ) ((r : ℤ) + e)
        (cap (j ≫ i) f'' (h ≫ g) (inner.paste_horiz outer) e β'')

/-- Compatibility of cycle-level cap maps with flat pullback of fixed relative
dimension. -/
def CompatibleWithFlatPullback
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    {f : X ⟶ Y} [LocallyOfFiniteType f.left] {r : ℕ} (cap : CapFamily δ f r) :
    Prop :=
  ∀ {X' Y' X'' Y'' : Over S}
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    [LocallyOfFiniteType X''.hom] [LocallyOfFiniteType Y''.hom]
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y) [LocallyOfFiniteType g.left]
    (outer : IsPullback i.left f'.left f.left g.left)
    (j : X'' ⟶ X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ Y')
    (inner : IsPullback j.left f''.left f'.left h.left) (c : ℕ)
    [Flat h.left] [Flat j.left]
    [RelativeDimension h.left c] [RelativeDimension j.left c]
    [LocallyOfFiniteType (f'.left ≫ Y'.hom)]
    [LocallyOfFiniteType (j.left ≫ f'.left ≫ Y'.hom)] (e : ℤ)
    (β : CycleGroup Y'.left (Y'.hom.relativeDimensionFunction δ) e),
    CycleGroup.toAlgebraicCycle
        ((f''.left ≫ Y''.hom).relativeDimensionFunction δ)
        ((r : ℤ) + (e + (c : ℤ)))
        (cap (j ≫ i) f'' (h ≫ g) (inner.paste_horiz outer) (e + c)
          (CycleGroup.flatPullback δ Y'' Y' h c e β)) =
      CycleGroup.toAlgebraicCycle
        ((j.left ≫ f'.left ≫ Y'.hom).relativeDimensionFunction δ)
        (((r : ℤ) + e) + (c : ℤ))
        (CycleGroup.flatPullbackAlong δ (j.left ≫ f'.left ≫ Y'.hom) (f'.left ≫ Y'.hom)
          j.left rfl c ((r : ℤ) + e) (cap i f' g outer e β))

/-- Compatibility of cycle-level cap maps with trivial-restriction Gysin along a
zero scheme and its cartesian pullback. -/
def CompatibleWithTrivialGysin
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    {f : X ⟶ Y} [LocallyOfFiniteType f.left] {r : ℕ} (cap : CapFamily δ f r) :
    Prop :=
  ∀ {X' Y' : Over S}
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y) [LocallyOfFiniteType g.left]
    (outer : IsPullback i.left f'.left f.left g.left)
    (ℒ : Y'.left.Modules) [Invertible ℒ] (s : ℒ.sections)
    (htriv : RingedSpace.IsTrivial ((Modules.pullback (Scheme.zeroSchemeι ℒ s)).obj ℒ)),
    let ℒX := (Modules.pullback f'.left).obj ℒ
    let sX := sectionsPullback f'.left ℒ s
    let j : Over.mk (Scheme.zeroSchemeι ℒX sX ≫ X'.hom) ⟶ X' :=
      Over.homMk (Scheme.zeroSchemeι ℒX sX)
    let h : Over.mk (Scheme.zeroSchemeι ℒ s ≫ Y'.hom) ⟶ Y' :=
      Over.homMk (Scheme.zeroSchemeι ℒ s)
    ∀ [LocallyOfFiniteType h.left] [LocallyOfFiniteType j.left]
      (f'' : Over.mk (Scheme.zeroSchemeι ℒX sX ≫ X'.hom) ⟶
        Over.mk (Scheme.zeroSchemeι ℒ s ≫ Y'.hom))
      (inner : IsPullback j.left f''.left f'.left h.left)
      (e : ℤ)
      (β : CycleGroup Y'.left (Y'.hom.relativeDimensionFunction δ) (e + 1)),
      CycleGroup.toAlgebraicCycle
          ((Scheme.zeroSchemeι ℒX sX ≫ f'.left ≫ Y'.hom).relativeDimensionFunction δ)
          ((r : ℤ) + e)
          (trivialGysin (f'.left ≫ Y'.hom) δ ℒX sX
            (isTrivial_zeroScheme_sectionsPullback f' ℒ s htriv) ((r : ℤ) + e)
            (CycleGroup.reindex ((f'.left ≫ Y'.hom).relativeDimensionFunction δ)
              (add_assoc (r : ℤ) e 1).symm (cap i f' g outer (e + 1) β))) =
        CycleGroup.toAlgebraicCycle
          ((f''.left ≫ (Over.mk (Scheme.zeroSchemeι ℒ s ≫ Y'.hom)).hom).relativeDimensionFunction δ)
          ((r : ℤ) + e)
          (cap (j ≫ i) f'' (h ≫ g) (inner.paste_horiz outer) e
            (trivialGysin Y'.hom δ ℒ s htriv e β))

/-- A cycle-level action of relative degree `r` consists of cartesian-square-indexed
cap maps compatible with proper pushforward, flat pullback, and trivial-restriction
Gysin. -/
structure Action
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [LocallyOfFiniteType f.left] (r : ℕ) where
  cap : CapFamily δ f r
  map_proper : CompatibleWithProperPushforward δ cap
  pullback_flat : CompatibleWithFlatPullback δ cap
  gysin_trivial : CompatibleWithTrivialGysin δ cap

/-- Two cycle-level actions are equal when their cap families agree. -/
@[ext]
theorem Action.ext
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    {f : X ⟶ Y} [LocallyOfFiniteType f.left] {r : ℕ} {c d : Action δ f r}
    (h : (c.cap : CapFamily δ f r) = (d.cap : CapFamily δ f r)) : c = d :=
  sorry

/-- The fibre product of `f : X ⟶ Y` along `g : Y' ⟶ Y`, as a scheme over `S`. -/
noncomputable abbrev pullbackOver
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) {Y' : Over S} (g : Y' ⟶ Y) :
    Over S :=
  Over.mk (pullback.snd f.left g.left ≫ Y'.hom)

/-- The first projection of `Y' ×_Y X` commutes with the structure morphisms to `S`. -/
theorem pullbackOverFst_w
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) {Y' : Over S} (g : Y' ⟶ Y) :
    pullback.fst f.left g.left ≫ X.hom =
      pullback.snd f.left g.left ≫ Y'.hom :=
  sorry

/-- The first projection of the fibre product `Y' ×_Y X` as a morphism over `S`. -/
noncomputable def pullbackOverFst
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) {Y' : Over S} (g : Y' ⟶ Y) :
    pullbackOver f g ⟶ X :=
  Over.homMk (pullback.fst f.left g.left) (pullbackOverFst_w f g)

/-- The second projection of the fibre product `Y' ×_Y X` as a morphism over `S`. -/
noncomputable def pullbackOverSnd
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) {Y' : Over S} (g : Y' ⟶ Y) :
    pullbackOver f g ⟶ Y' :=
  Over.homMk (pullback.snd f.left g.left)

/-- The chosen fibre-product square of `f` along `g` is cartesian. -/
theorem pullbackOver_isPullback
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) {Y' : Over S} (g : Y' ⟶ Y) :
    IsPullback (pullbackOverFst f g).left (pullbackOverSnd f g).left
      f.left g.left :=
  sorry

/-- The g-indexed operation of a cycle-level action, sending `Z_e(Y')` to
`Z_{r+e}(Y' ×_Y X)`. -/
noncomputable def capAlong
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    {f : X ⟶ Y} [LocallyOfFiniteType f.left] {r : ℕ} (c : Action δ f r)
    {Y' : Over S} (g : Y' ⟶ Y)
    [LocallyOfFiniteType Y'.hom] [LocallyOfFiniteType g.left] (e : ℤ) :
    CycleGroup Y'.left (Y'.hom.relativeDimensionFunction δ) e →+
      CycleGroup (pullback f.left g.left)
        ((pullback.snd f.left g.left ≫ Y'.hom).relativeDimensionFunction δ)
        ((r : ℤ) + e) :=
  c.cap (pullbackOverFst f g) (pullbackOverSnd f g) g
    (pullbackOver_isPullback f g) e

/-- Evaluating `capAlong` recovers the cap map on the chosen fibre-product square. -/
theorem capAlong_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    {f : X ⟶ Y} [LocallyOfFiniteType f.left] {r : ℕ} (c : Action δ f r)
    {Y' : Over S} (g : Y' ⟶ Y)
    [LocallyOfFiniteType Y'.hom] [LocallyOfFiniteType g.left] (e : ℤ)
    (β : CycleGroup Y'.left (Y'.hom.relativeDimensionFunction δ) e) :
    capAlong δ c g e β =
      c.cap (pullbackOverFst f g) (pullbackOverSnd f g) g
        (pullbackOver_isPullback f g) e β :=
  sorry

/-- The cap family of a fibre-cycle family applies fibre-cycle cap after base change
along each cartesian square. -/
noncomputable def relativeCycleCap
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [IsLocallyNoetherian Y.left] (f : X ⟶ Y) [LocallyOfFiniteType f.left]
    (r : ℕ) (α : f.left.FiberCycleFamily (r : ℤ)) : CapFamily δ f r :=
  fun {X' Y' : Over S} [LocallyOfFiniteType X'.hom]
      [LocallyOfFiniteType Y'.hom] i f' g [LocallyOfFiniteType g.left] hpb e ↦
    CyclesOnFibers.capHom Y'.hom f'.left δ
      (FiberCycleFamily.baseChange hpb α) e

/-- The cap family of a relative cycle commutes with proper pushforward. -/
theorem relativeCycleCap_map_proper
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [IsLocallyNoetherian Y.left] (f : X ⟶ Y) [LocallyOfFiniteType f.left]
    (r : ℕ) (α : f.left.FiberCycleFamily (r : ℤ)) (hα : IsRelative α) :
    CompatibleWithProperPushforward δ (relativeCycleCap δ f r α) :=
  sorry

/-- The cap family of a relative cycle commutes with flat pullback of fixed relative
dimension. -/
theorem relativeCycleCap_pullback_flat
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [IsLocallyNoetherian Y.left] (f : X ⟶ Y) [LocallyOfFiniteType f.left]
    (r : ℕ) (α : f.left.FiberCycleFamily (r : ℤ)) (hα : IsRelative α) :
    CompatibleWithFlatPullback δ (relativeCycleCap δ f r α) :=
  sorry

/-- The cap family of a relative cycle commutes with trivial-restriction Gysin maps. -/
theorem relativeCycleCap_gysin_trivial
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [IsLocallyNoetherian Y.left] (f : X ⟶ Y) [LocallyOfFiniteType f.left]
    (r : ℕ) (α : f.left.FiberCycleFamily (r : ℤ)) (hα : IsRelative α) :
    CompatibleWithTrivialGysin δ (relativeCycleCap δ f r α) :=
  sorry

/-- The cycle-level action associated to a relative `r`-cycle sends a test cycle to
the fibre-cycle cap of the base-changed family. -/
noncomputable def ofRelativeCycle
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [IsLocallyNoetherian Y.left] (f : X ⟶ Y) [LocallyOfFiniteType f.left]
    (r : ℕ) (α : f.left.FiberCycleFamily (r : ℤ)) (hα : IsRelative α) : Action δ f r where
  cap := relativeCycleCap δ f r α
  map_proper := relativeCycleCap_map_proper δ f r α hα
  pullback_flat := relativeCycleCap_pullback_flat δ f r α hα
  gysin_trivial := relativeCycleCap_gysin_trivial δ f r α hα

/-- The cap field of `ofRelativeCycle` is fibre-cycle cap of the base change of
`α`. -/
theorem ofRelativeCycle_cap
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [IsLocallyNoetherian Y.left] (f : X ⟶ Y) [LocallyOfFiniteType f.left]
    (r : ℕ) (α : f.left.FiberCycleFamily (r : ℤ)) (hα : IsRelative α)
    {X' Y' : Over S} [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y) [LocallyOfFiniteType g.left]
    (hpb : IsPullback i.left f'.left f.left g.left) (e : ℤ) :
    (ofRelativeCycle δ f r α hα).cap i f' g hpb e =
      CyclesOnFibers.capHom Y'.hom f'.left δ
        (FiberCycleFamily.baseChange hpb α) e :=
  sorry

/-- `capAlong` of the action of a relative cycle is fibre-cycle cap of the base
change of `α` along the chosen fibre product. -/
theorem ofRelativeCycle_capAlong
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [IsLocallyNoetherian Y.left] (f : X ⟶ Y) [LocallyOfFiniteType f.left]
    (r : ℕ) (α : f.left.FiberCycleFamily (r : ℤ)) (hα : IsRelative α)
    {Y' : Over S} (g : Y' ⟶ Y)
    [LocallyOfFiniteType Y'.hom] [LocallyOfFiniteType g.left] (e : ℤ)
    (β : CycleGroup Y'.left (Y'.hom.relativeDimensionFunction δ) e) :
    CycleGroup.toAlgebraicCycle
        ((pullback.snd f.left g.left ≫ Y'.hom).relativeDimensionFunction δ)
        ((r : ℤ) + e) (capAlong δ (ofRelativeCycle δ f r α hα) g e β) =
      CycleGroup.toAlgebraicCycle
        ((pullback.snd f.left g.left ≫ Y'.hom).relativeDimensionFunction δ)
        ((r : ℤ) + e)
        (CyclesOnFibers.cap Y'.hom (pullback.snd f.left g.left) δ
          (FiberCycleFamily.baseChange (IsPullback.of_hasPullback f.left g.left) α)
          β) :=
  sorry

/-- Every nonnegative-degree cycle-level action compatible with proper pushforward,
flat pullback, and trivial-restriction Gysin maps is induced by a relative cycle
after every locally finite type base change. -/
theorem exists_of_action
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [IsLocallyNoetherian Y.left] (f : X ⟶ Y) [LocallyOfFiniteType f.left]
    (r : ℕ) (c : Action δ f r) :
    ∃ α : f.left.FiberCycleFamily (r : ℤ),
      IsRelative α ∧
        ∀ {Y' : Over S} [LocallyOfFiniteType Y'.hom] (g : Y' ⟶ Y)
          [LocallyOfFiniteType g.left] (e : ℤ)
          (β : CycleGroup Y'.left (Y'.hom.relativeDimensionFunction δ) e),
          CycleGroup.toAlgebraicCycle
              ((pullback.snd f.left g.left ≫ Y'.hom).relativeDimensionFunction δ)
              ((r : ℤ) + e) (capAlong δ c g e β) =
            CycleGroup.toAlgebraicCycle
              ((pullback.snd f.left g.left ≫ Y'.hom).relativeDimensionFunction δ)
              ((r : ℤ) + e)
              (CyclesOnFibers.cap Y'.hom (pullback.snd f.left g.left) δ
                (FiberCycleFamily.baseChange
                  (IsPullback.of_hasPullback f.left g.left) α)
                β) :=
  sorry


end AlgebraicGeometry.RelativeCycle
