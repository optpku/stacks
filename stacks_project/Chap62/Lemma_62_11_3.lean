/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.Pullback
public import stacks_project.Chap62.Lemma_62_11_1_Cap
public import stacks_project.Chap62.Lemma_62_5_1_Operations

/-!
# Compatibility of the fibre-cycle action with flat base change

This file records that forming `α ∩ β` commutes with dimension-shifted
flat base change of the base and with flat pullback along a morphism of
fixed relative dimension.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom
namespace CyclesOnFibers

/-- The base change of `f : X ⟶ Y` along `g : S' ⟶ S`, as the morphism
`X ×_S S' ⟶ Y ×_S S'` induced by `Over.pullback`. -/
noncomputable abbrev overPullbackHom {S S' X Y : Scheme.{u}}
    (g : S' ⟶ S) (p : Y ⟶ S) (f : X ⟶ Y) :
    (pullback (f ≫ p) g : Scheme) ⟶ pullback p g :=
  ((Over.pullback g).map (Over.homMk f : Over.mk (f ≫ p) ⟶ Over.mk p)).left

/-- The structure morphism of the base-changed source is locally of finite
type whenever `X` is locally of finite type over `S`. -/
instance instLocallyOfFiniteType_overPullbackHom_comp {S S' X Y : Scheme.{u}}
    (g : S' ⟶ S) (p : Y ⟶ S) (f : X ⟶ Y) [LocallyOfFiniteType (f ≫ p)] :
    LocallyOfFiniteType (overPullbackHom g p f ≫ pullback.snd p g) :=
  sorry

/-- The square with top map `overPullbackHom g p f` is the cartesian
base change of `f` by `Y ×_S S' ⟶ Y`. -/
theorem isPullback_overPullbackHom {S S' X Y : Scheme.{u}}
    (g : S' ⟶ S) (p : Y ⟶ S) (f : X ⟶ Y) :
    IsPullback (pullback.fst (f ≫ p) g) (overPullbackHom g p f) f
      (pullback.fst p g) :=
  sorry

/-- The displayed map of an `Over.homMk` triangle is flat when the
underlying scheme morphism is flat. -/
instance instFlat_overHomMkLeft {S X Y : Scheme.{u}}
    (pY : Y ⟶ S) (φ : X ⟶ Y) [Flat φ] :
    Flat (Over.homMk φ : Over.mk (φ ≫ pY) ⟶ Over.mk pY).left :=
  sorry

/-- The displayed map of an `Over.homMk` triangle has the same relative
dimension as the underlying scheme morphism. -/
instance instRelativeDimension_overHomMkLeft {S X Y : Scheme.{u}}
    (pY : Y ⟶ S) (φ : X ⟶ Y) (c : ℕ) [RelativeDimension φ c] :
    RelativeDimension (Over.homMk φ : Over.mk (φ ≫ pY) ⟶ Over.mk pY).left c :=
  sorry

/-- Lemma 62.11.3 (1): forming `α ∩ β` commutes with dimension-shifted
flat base change of the base as in Situation 42.67.1. -/
@[stacks 0H68]
theorem cap_baseChange {S S' X Y : Scheme.{u}}
    [UniversallyCatenary S] [UniversallyCatenary S']
    (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
    (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ)
    (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
    (p : Y ⟶ S) (f : X ⟶ Y)
    [LocallyOfFiniteType p] [LocallyOfFiniteType f] [LocallyOfFiniteType (f ≫ p)]
    {r e : ℤ} (α : CyclesOnFibers f r)
    (β : CycleGroup Y (p.relativeDimensionFunction δ) e) :
    CycleGroup.toAlgebraicCycle
        ((overPullbackHom g p f ≫ pullback.snd p g).relativeDimensionFunction δ')
        (r + (e + c))
        (cap (pullback.snd p g) (overPullbackHom g p f) δ'
          (FiberCycleFamily.baseChange (isPullback_overPullbackHom g p f) α)
          (CycleGroup.baseChangePullback g δ δ' c hcompat p e β)) =
      CycleGroup.toAlgebraicCycle
        ((pullback.snd (f ≫ p) g).relativeDimensionFunction δ')
        ((r + e) + c)
        (CycleGroup.baseChangePullback g δ δ' c hcompat (f ≫ p) (r + e)
          (cap p f δ α β)) :=
    sorry

/-- Evaluating `cap_baseChange` at a point of `X ×_S S'` compares the
coefficients of both underlying algebraic cycles. -/
theorem cap_baseChange_apply {S S' X Y : Scheme.{u}}
    [UniversallyCatenary S] [UniversallyCatenary S']
    (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
    (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ)
    (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
    (p : Y ⟶ S) (f : X ⟶ Y)
    [LocallyOfFiniteType p] [LocallyOfFiniteType f] [LocallyOfFiniteType (f ≫ p)]
    {r e : ℤ} (α : CyclesOnFibers f r)
    (β : CycleGroup Y (p.relativeDimensionFunction δ) e)
    (x' : (pullback (f ≫ p) g : Scheme)) :
    CycleGroup.toAlgebraicCycle
        ((overPullbackHom g p f ≫ pullback.snd p g).relativeDimensionFunction δ')
        (r + (e + c))
        (cap (pullback.snd p g) (overPullbackHom g p f) δ'
          (FiberCycleFamily.baseChange (isPullback_overPullbackHom g p f) α)
          (CycleGroup.baseChangePullback g δ δ' c hcompat p e β)) x' =
      CycleGroup.toAlgebraicCycle
        ((pullback.snd (f ≫ p) g).relativeDimensionFunction δ')
        ((r + e) + c)
        (CycleGroup.baseChangePullback g δ δ' c hcompat (f ≫ p) (r + e)
          (cap p f δ α β)) x' :=
    sorry

/-- Lemma 62.11.3 (2): forming `α ∩ β` commutes with flat pullback along a
morphism `Y' ⟶ Y` that is locally of finite type of relative dimension `c`. -/
@[stacks 0H68]
theorem cap_flatPullback {S X Y Y' : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (p : Y ⟶ S) (f : X ⟶ Y)
    (h : Y' ⟶ Y) (c : ℕ) [Flat h] [RelativeDimension h c]
    [LocallyOfFiniteType p] [LocallyOfFiniteType f] [LocallyOfFiniteType (f ≫ p)]
    {r e : ℤ} (α : CyclesOnFibers f r)
    (β : CycleGroup Y (p.relativeDimensionFunction δ) e) :
    CycleGroup.toAlgebraicCycle
        ((pullback.snd f h ≫ h ≫ p).relativeDimensionFunction δ)
        (r + (e + (c : ℤ)))
        (cap (h ≫ p) (pullback.snd f h) δ
          (FiberCycleFamily.baseChange (IsPullback.of_hasPullback f h) α)
          (CycleGroup.flatPullback δ (Over.mk (h ≫ p)) (Over.mk p)
            (Over.homMk h : Over.mk (h ≫ p) ⟶ Over.mk p) c e β)) =
      CycleGroup.toAlgebraicCycle
        ((pullback.fst f h ≫ f ≫ p).relativeDimensionFunction δ)
        ((r + e) + (c : ℤ))
        (CycleGroup.flatPullback δ (Over.mk (pullback.fst f h ≫ f ≫ p))
          (Over.mk (f ≫ p))
          (Over.homMk (pullback.fst f h) :
            Over.mk (pullback.fst f h ≫ f ≫ p) ⟶ Over.mk (f ≫ p))
          c (r + e) (cap p f δ α β)) :=
    sorry

/-- Evaluating `cap_flatPullback` at a point of `X ×_Y Y'` compares the
coefficients of both underlying algebraic cycles. -/
theorem cap_flatPullback_apply {S X Y Y' : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (p : Y ⟶ S) (f : X ⟶ Y)
    (h : Y' ⟶ Y) (c : ℕ) [Flat h] [RelativeDimension h c]
    [LocallyOfFiniteType p] [LocallyOfFiniteType f] [LocallyOfFiniteType (f ≫ p)]
    {r e : ℤ} (α : CyclesOnFibers f r)
    (β : CycleGroup Y (p.relativeDimensionFunction δ) e)
    (x' : (pullback f h : Scheme)) :
    CycleGroup.toAlgebraicCycle
        ((pullback.snd f h ≫ h ≫ p).relativeDimensionFunction δ)
        (r + (e + (c : ℤ)))
        (cap (h ≫ p) (pullback.snd f h) δ
          (FiberCycleFamily.baseChange (IsPullback.of_hasPullback f h) α)
          (CycleGroup.flatPullback δ (Over.mk (h ≫ p)) (Over.mk p)
            (Over.homMk h : Over.mk (h ≫ p) ⟶ Over.mk p) c e β)) x' =
      CycleGroup.toAlgebraicCycle
        ((pullback.fst f h ≫ f ≫ p).relativeDimensionFunction δ)
        ((r + e) + (c : ℤ))
        (CycleGroup.flatPullback δ (Over.mk (pullback.fst f h ≫ f ≫ p))
          (Over.mk (f ≫ p))
          (Over.homMk (pullback.fst f h) :
            Over.mk (pullback.fst f h ≫ f ≫ p) ⟶ Over.mk (f ≫ p))
          c (r + e) (cap p f δ α β)) x' :=
    sorry

end CyclesOnFibers
end AlgebraicGeometry.Scheme.Hom
