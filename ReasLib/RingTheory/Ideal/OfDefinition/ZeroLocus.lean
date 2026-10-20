/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.OfDefinition
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.CrossRefAttribute

/-!
# Zero loci of principal ideals of definition

This leaf relates the algebraic radical criterion for a principal ideal of definition to its
prime-spectrum zero locus.  Keeping this bridge separate avoids making the algebraic
`Ideal.IsIdealOfDefinition` owner depend on spectrum topology.

@stack 00KK
-/

@[expose] public section

universe u

open Ideal IsLocalRing

namespace PrimeSpectrum

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- A singleton zero locus is the closed point exactly when the radical of the generated ideal is
the maximal ideal.  This bridge is independent of Noetherian hypotheses. -/
@[stacks 00KK "zero-locus and principal radical bridge"]
theorem zeroLocus_singleton_eq_closedPoint_iff_radical (x : R) :
    zeroLocus ({x} : Set R) = ({IsLocalRing.closedPoint R} : Set (PrimeSpectrum R)) ↔
      IsLocalRing.maximalIdeal R = (Ideal.span ({x} : Set R)).radical := sorry

end PrimeSpectrum

end
