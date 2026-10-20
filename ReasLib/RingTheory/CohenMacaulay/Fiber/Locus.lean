/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.FinitePresentation
public import ReasLib.RingTheory.CohenMacaulay.Locus
public import ReasLib.RingTheory.KrullDimension.Relative
public import ReasLib.RingTheory.RingHom.Fiber.FiniteType
public import ReasLib.RingTheory.RingHom.Fiber.Local
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Cohen--Macaulay loci of fibers

@stack 00RH
@stack 00RI

This leaf owns the locus on an affine target where its residue-field local
fiber is Cohen--Macaulay.  The exact-relative-dimension refinement is a
separate set owner, so topology and base-change results can use it without
repeating a raw intersection of predicates.
-/

universe u v

namespace PrimeSpectrum

section

variable (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
variable [Algebra.FiniteType R S]

/-- The locus in `Spec(S)` where the local ring of the residue-field fiber of `S/R` is
Cohen--Macaulay. -/
@[stacks 00RH "Cohen-Macaulay fiber locus"]
def cohenMacaulayFiberLocus : Set (PrimeSpectrum S) :=
  {q | Module.CohenMacaulay (fiberLocalRingAt R S q) (fiberLocalRingAt R S q)}

/-- Membership in `cohenMacaulayFiberLocus R S` is Cohen--Macaulayness of the corresponding
local fiber ring. -/
@[stacks 00RH "membership in the Cohen-Macaulay fiber locus"]
lemma mem_cohenMacaulayFiberLocus (q : PrimeSpectrum S) :
    q ∈ cohenMacaulayFiberLocus R S ↔
      Module.CohenMacaulay (fiberLocalRingAt R S q) (fiberLocalRingAt R S q) :=
  Iff.rfl

attribute [simp] mem_cohenMacaulayFiberLocus

/-- The local-fiber-ring formulation of Cohen--Macaulayness is equivalent to membership in the
Cohen--Macaulay locus of the ambient residue-field fiber at its canonical prime. -/
@[stacks 00RH "fiber-ring description of the Cohen-Macaulay fiber locus"]
lemma mem_cohenMacaulayFiberLocus_iff_mem_cohenMacaulayLocus (q : PrimeSpectrum S) :
    q ∈ cohenMacaulayFiberLocus R S ↔
      fiberPrimeAt R S q ∈ cohenMacaulayLocus ((q.asIdeal.under R).Fiber S) := sorry

/-- The stratum where the local residue-field fiber is Cohen--Macaulay and has exact relative
dimension `d`. -/
@[stacks 00RH "Cohen-Macaulay fiber dimension stratum"]
def cohenMacaulayFiberDimensionStratum (d : ℕ) : Set (PrimeSpectrum S) :=
  cohenMacaulayFiberLocus R S ∩
    {q | relativeDimensionAt R S q = (d : WithBot ℕ∞)}

/-- Membership in a Cohen--Macaulay fiber dimension stratum is the conjunction of the
Cohen--Macaulay fiber condition and the exact relative-dimension equation. -/
@[stacks 00RH "membership in a Cohen-Macaulay fiber dimension stratum"]
lemma mem_cohenMacaulayFiberDimensionStratum (d : ℕ) (q : PrimeSpectrum S) :
    q ∈ cohenMacaulayFiberDimensionStratum R S d ↔
      q ∈ cohenMacaulayFiberLocus R S ∧
        relativeDimensionAt R S q = (d : WithBot ℕ∞) :=
  Iff.rfl

attribute [simp] mem_cohenMacaulayFiberDimensionStratum

end

namespace CohenMacaulayFiberDimensionStratum

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [a : Algebra R S]
variable [hfinitePresentation : Algebra.FinitePresentation R S] [hflat : Module.Flat R S]

include hfinitePresentation hflat

/-- For a flat finitely presented algebra, every Cohen--Macaulay fiber dimension
stratum is open. -/
@[stacks 00RH "openness of a Cohen-Macaulay fiber dimension stratum"]
lemma isOpen_of_finitePresentation_flat (d : ℕ) :
    IsOpen (cohenMacaulayFiberDimensionStratum R S d) := sorry

end CohenMacaulayFiberDimensionStratum

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FinitePresentation R S] [Module.Flat R S]

/-- The Cohen--Macaulay locus of residue-field local fibers of a flat finitely
presented algebra is open. -/
@[stacks 00RI "openness of the Cohen-Macaulay fiber locus"]
theorem isOpen_cohenMacaulayFiberLocus_of_finitePresentation_flat :
    IsOpen (cohenMacaulayFiberLocus R S) := sorry

end

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FiniteType R S]

/-- On a finite-type residue-field fiber, the induced Cohen--Macaulay fiber locus
is dense in the corresponding set-theoretic fiber of `Spec(S) → Spec(R)`. -/
@[stacks 00RI "fiberwise density of the Cohen-Macaulay fiber locus"]
theorem dense_preimage_cohenMacaulayFiberLocus_of_fiberFiniteType
    (p : PrimeSpectrum R) [Algebra.FiniteType p.asIdeal.ResidueField (p.asIdeal.Fiber S)] :
    Dense
      (((↑) : PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p} → PrimeSpectrum S) ⁻¹'
        cohenMacaulayFiberLocus R S) := sorry

end

end PrimeSpectrum
