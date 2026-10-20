/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Catenary.Basic
public import ReasLib.RingTheory.CohenMacaulay.SerreCondition
public import ReasLib.Topology.KrullDimension.Equidimensional

@[expose] public section

universe u

namespace SerreConditionS

/-- The prime spectrum of a Noetherian local ring that is catenary and satisfies Serre's
condition `(S₂)` is equidimensional. -/
@[stacks 0FIW]
instance instEquidimensionalSpacePrimeSpectrum
    {A : Type u} [CommRing A] [IsLocalRing A] [IsCatenaryRing A] [SerreConditionS A 2] :
    TopologicalSpace.EquidimensionalSpace (PrimeSpectrum A) := sorry

end SerreConditionS
