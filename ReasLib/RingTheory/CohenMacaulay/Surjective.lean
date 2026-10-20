/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CohenMacaulay.Module
public import ReasLib.RingTheory.Depth.Surjective
public import ReasLib.RingTheory.KrullDimension.Module.Surjective

/-!
# Cohen-Macaulay Modules under Surjective Scalar Maps

@stack 0AAD

Surjective scalar restriction preserves both support dimension and local depth,
so the Cohen-Macaulay condition may be transported in either direction.
-/

@[expose] public section

universe u v w

namespace Module

namespace CohenMacaulay

variable {R : Type u} {S : Type v} {N : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S]
variable [IsNoetherianRing R] [IsNoetherianRing S]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

/-- Lemma 10.103.6, tag `0AAD`: Cohen-Macaulayness is unchanged by
restricting scalars along a surjective map of Noetherian local rings. -/
@[stacks 0AAD]
theorem iff_restrictScalars_of_surjective
    (hsurj : Function.Surjective (algebraMap R S)) :
    CohenMacaulay S N ↔ CohenMacaulay R N := sorry

/-- A Cohen-Macaulay module remains Cohen-Macaulay after restricting scalars
along a surjective map of Noetherian local rings. -/
theorem restrictScalars_of_surjective
    (hsurj : Function.Surjective (algebraMap R S)) [CohenMacaulay S N] :
    CohenMacaulay R N := sorry

/-- Cohen-Macaulayness over the source descends to the target of a surjective
map of Noetherian local rings. -/
theorem of_restrictScalars_of_surjective
    (hsurj : Function.Surjective (algebraMap R S)) [CohenMacaulay R N] :
    CohenMacaulay S N := sorry

end CohenMacaulay

end Module
