/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import ReasLib.RingTheory.Depth

/-!
# Depth over a Finite Algebra

This file compares depth over a local base ring with the depths obtained by
localizing a finite algebra at its maximal ideals.
-/

@[expose] public section

universe u v w

namespace Module

/-- Chap10 Lemma 10 72 11, tag `0AUK`: for a finite algebra `S` over a
Noetherian local ring `R` and a finite `S`-module `N`, the depth of `N` over
`R` is the infimum of the depths of `N` at the maximal ideals of `S`.

Finiteness of `N` over `R` follows from the two displayed finiteness
instances and is therefore not part of the public parameter list. -/
@[stacks 0AUK]
theorem moduleDepth_eq_iInf_atMaximal
    {R : Type u} {S : Type v} {N : Type w}
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.Finite R S] [Module.Finite S N] :
    moduleDepth R N =
      ⨅ m : MaximalSpectrum S,
        moduleDepth (Localization.AtPrime m.asIdeal)
          (LocalizedModule.AtPrime m.asIdeal N) := sorry

end Module
