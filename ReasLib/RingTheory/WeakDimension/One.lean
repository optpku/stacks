/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.RingTheory.Flat.Ideal
public import ReasLib.RingTheory.Valuation.Locally
public import ReasLib.RingTheory.WeakDimension
import Mathlib.Tactic.CrossRefAttribute

/-!
# Weak dimension at most one

This leaf owns the reusable characterizations of weak dimension at most one.  The individual
consequences accompany the aggregate `List.TFAE`, so downstream developments do not have to
reconstruct paths through a five-clause equivalence or install temporary instances.
@stack 092S
-/

@[expose] public section

open CategoryTheory

universe u v

namespace HasWeakDimensionLE

variable {R : Type u} [CommRing R]

/-- Weak dimension at most one makes every ideal flat. -/
@[stacks 092S "weak dimension one gives flat ideals"]
theorem ideal_flat (h : HasWeakDimensionLE R 1) (I : Ideal R) :
    Module.Flat R I := sorry

/-- Under weak dimension at most one, every submodule of a flat module is flat. -/
@[stacks 092S "weak dimension one gives flat submodules"]
theorem submodule_flat (h : HasWeakDimensionLE R 1)
    {M : Type v} [AddCommMonoid M] [Module R M]
    (hM : Module.Flat R M) (N : Submodule R M) :
    Module.Flat R N := sorry

/-- Submodules of flat modules are canonically flat over a ring of weak dimension at most one. -/
@[stacks 092S "canonical flatness of submodules in weak dimension one"]
instance instSubmoduleFlat [HasWeakDimensionLE R 1]
    {M : Type v} [AddCommMonoid M] [Module R M] [Module.Flat R M]
    (N : Submodule R M) : Module.Flat R N := sorry

/-- A ring of weak dimension at most one is locally valuation. -/
@[stacks 092S "weak dimension one gives valuation localizations"]
theorem locallyValuation (h : HasWeakDimensionLE R 1) :
    Ring.LocallyValuation R := sorry

/-- Weak dimension at most one is equivalent to flatness of every ideal. -/
@[stacks 092S "weak dimension one iff all ideals are flat"]
theorem one_iff_ideals_flat :
    HasWeakDimensionLE R 1 ↔ ∀ I : Ideal R, Module.Flat R I := sorry

/-- Weak dimension at most one is detected on finitely generated ideals. -/
@[stacks 092S "weak dimension one iff finitely generated ideals are flat"]
theorem one_iff_fg_ideals_flat :
    HasWeakDimensionLE R 1 ↔
      ∀ I : Ideal R, I.FG → Module.Flat R I := sorry

/-- Weak dimension at most one is equivalent to flatness of submodules of flat modules. -/
@[stacks 092S "weak dimension one iff submodules of flat modules are flat"]
theorem one_iff_submodules_flat :
    HasWeakDimensionLE R 1 ↔
      ∀ (M : ModuleCat.{u} R) [Module.Flat R M] (N : Submodule R M),
        Module.Flat R N := sorry

/-- Weak dimension at most one is equivalent to having valuation rings at all prime
localizations. -/
@[stacks 092S "weak dimension one iff locally valuation"]
theorem one_iff_locallyValuation :
    HasWeakDimensionLE R 1 ↔ Ring.LocallyValuation R := sorry

/-- The ideal, submodule, and prime-local characterizations of weak dimension at most one. -/
@[stacks 092S "weak dimension one characterizations"]
theorem one_tfae :
    List.TFAE
      [ HasWeakDimensionLE R 1,
        ∀ I : Ideal R, Module.Flat R I,
        ∀ I : Ideal R, I.FG → Module.Flat R I,
        ∀ (M : ModuleCat.{u} R) [Module.Flat R M] (N : Submodule R M),
          Module.Flat R N,
        Ring.LocallyValuation R ] := sorry

end HasWeakDimensionLE
