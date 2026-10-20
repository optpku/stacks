/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RelativeCycle.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Cover.H

/-!
# Descent of properness of relative cycles along h coverings

Properness of a relative cycle over a locally Noetherian base can be checked
after base change along every member of an h covering.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

open Scheme.Hom CyclesOnFibers

/-- A relative `r`-cycle for a locally finite type morphism over a locally
Noetherian base is proper if and only if its base change along every member
of an h covering is proper. -/
@[stacks 0H63]
theorem proper_iff_hCovering_baseChange {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ)
    (α : CyclesOnFibers f r) (hα : RelativeCycle.IsRelative α)
    {ι : Type v} (family : ι → Over S) [Scheme.HCovering family] :
    Proper α ↔ ∀ i, Proper
      (Scheme.Hom.FiberCycleFamily.baseChange (IsPullback.of_hasPullback f (family i).hom) α) :=
  sorry

/-- A relative `r`-cycle for a locally finite type morphism over a locally
Noetherian base is proper if its base change along every member of an h
covering is proper. -/
theorem proper_of_hCovering_baseChange {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ)
    (α : CyclesOnFibers f r) (hα : RelativeCycle.IsRelative α)
    {ι : Type v} (family : ι → Over S) [Scheme.HCovering family]
    (h : ∀ i, Proper
      (Scheme.Hom.FiberCycleFamily.baseChange (IsPullback.of_hasPullback f (family i).hom) α)) :
    Proper α :=
  (proper_iff_hCovering_baseChange f r α hα family).mpr h

end AlgebraicGeometry
