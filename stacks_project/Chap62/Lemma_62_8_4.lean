/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RelativeCycle.EffectiveBaseChange
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 62.8.4: if `S` is locally Noetherian and `f : X ⟶ S` is locally of
finite type, then a relative `r`-cycle `α` on `X / S` is effective if and only
if its base change along a surjective morphism `g : S' ⟶ S` is effective. -/
@[stacks 0H5U] #check (AlgebraicGeometry.isEffective_iff_baseChange :
    ∀ {X S S' : Scheme.{u}} (f : X ⟶ S)
      [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ)
      (α : Scheme.Hom.CyclesOnFibers f r) (hα : RelativeCycle.IsRelative α)
      (g : S' ⟶ S) [Surjective g],
      Scheme.Hom.CyclesOnFibers.IsEffective α ↔
        Scheme.Hom.CyclesOnFibers.IsEffective
          (Scheme.Hom.FiberCycleFamily.baseChange (IsPullback.of_hasPullback f g) α))
