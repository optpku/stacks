/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RelativeCycle.Proper
import StacksCheckRecall

/-!
# Functoriality of proper relative cycles

Base change along an arbitrary morphism of bases preserves properness of
relative `r`-cycles.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 62.9.2: if `f : X ⟶ S` is locally of finite type, `S` is locally
Noetherian, and `α` is a proper relative `r`-cycle on `X / S`, then any base
change of `α` along `g : S' ⟶ S` is proper. -/
@[stacks 0H62] #check (AlgebraicGeometry.proper_baseChange :
  ∀ {X S S' : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (g : S' ⟶ S) (r : ℕ)
    (α : Scheme.Hom.CyclesOnFibers f r),
    RelativeCycle.IsRelative (r := r) α → Scheme.Hom.CyclesOnFibers.Proper α →
      Scheme.Hom.CyclesOnFibers.Proper
        (Scheme.Hom.FiberCycleFamily.baseChange (IsPullback.of_hasPullback f g) α))
