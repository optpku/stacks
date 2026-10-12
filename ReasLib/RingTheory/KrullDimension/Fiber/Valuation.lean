/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.KrullDimension.Fiber
public import ReasLib.Topology.KrullDimension.Equidimensional

@[expose] public section

/-!
# Fibers over valuation rings

This leaf records the dimension comparison between the closed and generic
residue-field fibers of a finite-type domain over a valuation ring.
-/

noncomputable section

open TopologicalSpace IsLocalRing

universe u v

namespace ValuationRing.SpecialFiber

variable {R : Type u} {S : Type v}
variable [CommRing R] [IsDomain R] [ValuationRing R]
variable [CommRing S] [IsDomain S] [Algebra R S] [Algebra.FiniteType R S]

/-- Every irreducible component of the closed fiber of a finite-type domain over a valuation
ring has topological Krull dimension equal to that of the generic fiber. -/
@[stacks 00QK "component dimension of a valuation-ring special fiber"]
theorem componentTopologicalKrullDim_eq_genericFiber
    (hRS : Function.Injective (algebraMap R S))
    (Z : irreducibleComponents (PrimeSpectrum (Ideal.Fiber (maximalIdeal R) S))) :
    topologicalKrullDim (Z : Set (PrimeSpectrum (Ideal.Fiber (maximalIdeal R) S))) =
      ringKrullDim (Ideal.Fiber (⊥ : Ideal R) S) := sorry

/-- The closed fiber of a finite-type domain over a valuation ring is equidimensional when the
structure map is injective. -/
@[stacks 00QK "equidimensional valuation-ring special fiber"]
theorem equidimensional_of_finiteType
    (hRS : Function.Injective (algebraMap R S)) :
    EquidimensionalSpace (PrimeSpectrum (Ideal.Fiber (maximalIdeal R) S)) := sorry

/-- If the closed fiber of a finite-type domain over a valuation ring is nontrivial, its Krull
dimension equals the Krull dimension of the generic fiber. -/
@[stacks 00QK "dimension of a valuation-ring special fiber"]
theorem ringKrullDim_eq_genericFiber_of_finiteType
    (hRS : Function.Injective (algebraMap R S))
    [Nontrivial (Ideal.Fiber (maximalIdeal R) S)] :
    ringKrullDim (Ideal.Fiber (maximalIdeal R) S) =
      ringKrullDim (Ideal.Fiber (⊥ : Ideal R) S) := sorry

end ValuationRing.SpecialFiber
