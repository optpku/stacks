/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CohenMacaulay.Module

@[expose] public section

/-!
# Maximal Cohen-Macaulay Modules

The local maximal Cohen-Macaulay condition and its bridge to ordinary Cohen-Macaulayness.

@stack 00NF
-/

universe u v

open IsLocalRing

section

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

namespace Module

/-- Definition 10.103.8: a finite `R`-module over a Noetherian local ring is maximal
Cohen-Macaulay when its depth equals the Krull dimension of `R`. -/
@[stacks 00NF]
class MaximalCohenMacaulay (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] : Prop extends Module.Finite R M where
  depth_eq_ringKrullDim : .some (moduleDepth R M) = ringKrullDim R

namespace MaximalCohenMacaulay

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- A maximal Cohen-Macaulay module is nontrivial. -/
theorem nontrivial (h : MaximalCohenMacaulay R M) : Nontrivial M := sorry

/-- A maximal Cohen-Macaulay module has support dimension equal to the Krull dimension of the
base ring. -/
theorem supportDim_eq_ringKrullDim (h : MaximalCohenMacaulay R M) :
    Module.supportDim R M = ringKrullDim R := sorry

/-- A maximal Cohen-Macaulay module is Cohen-Macaulay. -/
theorem toCohenMacaulay (h : MaximalCohenMacaulay R M) : Module.CohenMacaulay R M := sorry

end MaximalCohenMacaulay

/-- The maximal Cohen-Macaulay condition supplies the Cohen-Macaulay instance. -/
instance cohenMacaulay_of_maximalCohenMacaulay [MaximalCohenMacaulay R M] :
    Module.CohenMacaulay R M := sorry

end Module

end
