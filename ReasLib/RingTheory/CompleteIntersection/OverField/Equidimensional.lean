/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import ReasLib.RingTheory.CompleteIntersection.OverField
public import ReasLib.Topology.KrullDimension.Equidimensional

@[expose] public section

/-!
# Equidimensionality of Complete Intersections over a Field

This module records the equidimensionality of the prime spectrum of a global
complete-intersection algebra over a field.
-/

universe u v

namespace IsGlobalCompleteIntersection

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S]

/-- The prime spectrum of a global complete-intersection algebra over a field is
equidimensional. -/
theorem equidimensionalSpace (hS : IsGlobalCompleteIntersection k S) :
    TopologicalSpace.EquidimensionalSpace (PrimeSpectrum S) := sorry

end IsGlobalCompleteIntersection
