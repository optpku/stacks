/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.Cap.BaseChange

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

/- Lemma 62.11.3: compatibility with flat base change. -/
@[stacks 0H68] #check (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.cap_baseChange :
    ∀ {S S' X Y : Scheme.{u}}
    [UniversallyCatenary S] [UniversallyCatenary S']
    (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
    (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ)
    (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
    (p : Y ⟶ S) (f : X ⟶ Y)
    [LocallyOfFiniteType p] [LocallyOfFiniteType f]
    {r e : ℤ} (α : CyclesOnFibers f r)
    (β : CycleGroup Y (p.relativeDimensionFunction δ) e),
    CycleGroup.toAlgebraicCycle
        ((Scheme.Pullback.overMap g p f ≫ pullback.snd p g).relativeDimensionFunction δ')
        (r + (e + c))
        (cap (pullback.snd p g) (Scheme.Pullback.overMap g p f) δ'
          (FiberCycleFamily.baseChange (Scheme.Pullback.isPullback_overMap g p f) α)
          (CycleGroup.baseChangePullback g δ δ' c hcompat p e β)) =
      CycleGroup.toAlgebraicCycle
        ((pullback.snd (f ≫ p) g).relativeDimensionFunction δ')
        ((r + e) + c)
        (CycleGroup.baseChangePullback g δ δ' c hcompat (f ≫ p) (r + e)
          (cap p f δ α β)))

/- Lemma 62.11.3: compatibility with flat pullback. -/
@[stacks 0H68] #check (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.cap_flatPullback :
    ∀ {S X Y Y' : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (p : Y ⟶ S) (f : X ⟶ Y)
    (h : Y' ⟶ Y) (c : ℕ) [Flat h] [RelativeDimension h c]
    [LocallyOfFiniteType p] [LocallyOfFiniteType f]
    {r e : ℤ} (α : CyclesOnFibers f r)
    (β : CycleGroup Y (p.relativeDimensionFunction δ) e),
    CycleGroup.toAlgebraicCycle
        ((pullback.snd f h ≫ h ≫ p).relativeDimensionFunction δ)
        (r + (e + (c : ℤ)))
        (cap (h ≫ p) (pullback.snd f h) δ
          (FiberCycleFamily.baseChange (IsPullback.of_hasPullback f h) α)
          (CycleGroup.flatPullbackAlong δ (h ≫ p) p h rfl c e β)) =
      CycleGroup.toAlgebraicCycle
        ((pullback.fst f h ≫ f ≫ p).relativeDimensionFunction δ)
        ((r + e) + (c : ℤ))
        (CycleGroup.flatPullbackAlong δ (pullback.fst f h ≫ f ≫ p)
          (f ≫ p) (pullback.fst f h) rfl c (r + e) (cap p f δ α β)))

end CyclesOnFibers
end AlgebraicGeometry.Scheme.Hom
