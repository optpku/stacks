/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RelativeCycle.Proper.HCovering
import StacksCheckRecall

/-!
# Descent of properness of relative cycles along h coverings

A relative `r`-cycle on `X / S` is proper if and only if every base change
along an h covering of `S` is proper.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme.Hom
open CyclesOnFibers

universe u v

/- Lemma 62.9.3: properness of a relative cycle is equivalent to properness
after base change along every member of an h covering. -/
@[stacks 0H63]
#check (AlgebraicGeometry.proper_iff_hCovering_baseChange :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ)
    (α : CyclesOnFibers f r) (hα : RelativeCycle.IsRelative α)
    {ι : Type v} (family : ι → Over S) [Scheme.HCovering family],
    Proper α ↔ ∀ i, Proper
      (Scheme.Hom.FiberCycleFamily.baseChange (IsPullback.of_hasPullback f (family i).hom) α))
