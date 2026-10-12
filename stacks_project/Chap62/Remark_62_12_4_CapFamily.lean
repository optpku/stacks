/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import stacks_project.Chap62.Lemma_62_11_1_Cap
public import stacks_project.Chap62.Lemma_62_5_1_Operations
public import stacks_project.Chap62.Lemma_62_6_6_Relative
public import stacks_project.Chap62.Lemma_62_12_2

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

/-- Flat pullback of cycles along a scheme morphism `φ` displayed over `S`. -/
noncomputable def flatPullbackAlong
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Xs Ys : Scheme.{u}} (pX : Xs ⟶ S) (pY : Ys ⟶ S)
    (φ : Xs ⟶ Ys) (hφ : φ ≫ pY = pX) (c : ℕ)
    [Flat φ] [RelativeDimension φ c]
    [LocallyOfFiniteType pX] [LocallyOfFiniteType pY] (k : ℤ) :
    CycleGroup Ys (pY.relativeDimensionFunction δ) k →+
      CycleGroup Xs (pX.relativeDimensionFunction δ) (k + (c : ℤ)) :=
  CycleGroup.flatPullback δ (Over.mk pX) (Over.mk pY) (Over.homMk φ hφ) c k

/-- Unfolding `flatPullbackAlong` recovers `CycleGroup.flatPullback` of the
displayed over-morphism. -/
theorem flatPullbackAlong_eq
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Xs Ys : Scheme.{u}} (pX : Xs ⟶ S) (pY : Ys ⟶ S)
    (φ : Xs ⟶ Ys) (hφ : φ ≫ pY = pX) (c : ℕ)
    [Flat φ] [RelativeDimension φ c]
    [LocallyOfFiniteType pX] [LocallyOfFiniteType pY] (k : ℤ) :
    flatPullbackAlong δ pX pY φ hφ c k =
      CycleGroup.flatPullback δ (Over.mk pX) (Over.mk pY) (Over.homMk φ hφ) c k :=
  sorry

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
        (flatPullbackAlong δ (j.left ≫ f'.left ≫ Y'.hom) (f'.left ≫ Y'.hom)
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
    (htriv : RingedSpace.IsTrivial (CyclesOnFibers.gysinRestrictionModule ℒ s)),
    let ℒX := CyclesOnFibers.gysinPullbackModule f' ℒ
    let sX := CyclesOnFibers.gysinPullbackSection f' ℒ s
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
          ((f''.left ≫ Scheme.zeroSchemeι ℒ s ≫ Y'.hom).relativeDimensionFunction δ)
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

/-- The structure morphism of the fibre product over `S` is locally of finite type
when `Y' ⟶ S` and `X ⟶ Y` are. -/
instance instLocallyOfFiniteType_pullbackOver
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) {Y' : Over S} (g : Y' ⟶ Y)
    [LocallyOfFiniteType Y'.hom] [LocallyOfFiniteType f.left] :
    LocallyOfFiniteType (pullbackOver f g).hom :=
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

/-- The cycle-level action associated to a relative `r`-cycle, sending a test
cycle to the fibre-cycle cap of the base change of `α`. -/
noncomputable def ofRelativeCycle
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [IsLocallyNoetherian Y.left] (f : X ⟶ Y) [LocallyOfFiniteType f.left]
    (r : ℕ) (α : Family f.left r) (hα : IsRelative α) : Action δ f r where
  cap := fun {X' Y' : Over S} [LocallyOfFiniteType X'.hom]
      [LocallyOfFiniteType Y'.hom] i f' g [LocallyOfFiniteType g.left] hpb e ↦
    CyclesOnFibers.capHom Y'.hom f'.left δ
      (FiberCycleFamily.baseChange hpb α) e
  map_proper := sorry
  pullback_flat := sorry
  gysin_trivial := sorry

/-- The cap field of `ofRelativeCycle` is fibre-cycle cap of the base change of
`α`. -/
theorem ofRelativeCycle_cap
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [IsLocallyNoetherian Y.left] (f : X ⟶ Y) [LocallyOfFiniteType f.left]
    (r : ℕ) (α : Family f.left r) (hα : IsRelative α)
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
    (r : ℕ) (α : Family f.left r) (hα : IsRelative α)
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

end AlgebraicGeometry.RelativeCycle
