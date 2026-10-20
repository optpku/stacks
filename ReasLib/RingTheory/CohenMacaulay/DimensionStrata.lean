/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.KrullDimension.Stratum
public import ReasLib.Topology.KrullDimension.Equidimensional
public import ReasLib.RingTheory.CohenMacaulay.Ring
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Cohen--Macaulay dimension strata

@stack 00OV

This leaf owns the finite clopen stratification, its equidimensionality, and
the resulting product decomposition for finite-type Cohen--Macaulay algebras
over fields. The underlying topological stratum is owned by
`PrimeSpectrum.dimensionStratum`.
-/

universe u v

namespace Algebra.CohenMacaulay

variable {k : Type u} {S : Type v}
variable [Field k] [CommRing S] [Algebra k S]
variable [Algebra.FiniteType k S] [CohenMacaulayRing S]

-- The first two conclusions mention only `S`, but their finite-type-over-a-field
-- hypotheses are part of the source theorem.
include k

/-- Lemma 10.114.7 (1), tag `00OV`: the nonempty local-dimension strata form
a finite clopen cover of the prime spectrum. -/
@[stacks 00OV "(1), finite clopen dimension-stratum cover"]
theorem existsFiniteClopenDimensionStrataCover :
    ∃ D : Finset ℕ,
      (⋃ d : D, PrimeSpectrum.dimensionStratum S (d : ℕ)) = Set.univ ∧
        ∀ d : D,
          (PrimeSpectrum.dimensionStratum S (d : ℕ)).Nonempty ∧
            IsClopen (PrimeSpectrum.dimensionStratum S (d : ℕ)) := sorry

/-- Lemma 10.114.7 (3), tag `00OV`: every nonempty dimension-`d` stratum is
equidimensional of dimension `d`. -/
@[stacks 00OV "(3), equidimensional dimension strata"]
theorem dimensionStratum_equidimensional_and_dimension_eq (d : ℕ)
    (hd : (PrimeSpectrum.dimensionStratum S d).Nonempty) :
    TopologicalSpace.EquidimensionalSpace (PrimeSpectrum.dimensionStratum S d) ∧
      topologicalKrullDim (PrimeSpectrum.dimensionStratum S d) = d := sorry

/-- Lemma 10.114.7, tag 00OV: a finite-type Cohen--Macaulay algebra over a
field admits a finite product decomposition indexed by its nonempty local
dimension strata; each factor cuts out its stratum and has the corresponding
maximal-ideal height. -/
@[stacks 00OV "product decomposition by dimension strata"]
theorem existsDimensionStrataProduct :
    ∃ (D : Finset ℕ)
      (_ : ∀ d : ℕ, d ∈ D ↔ (PrimeSpectrum.dimensionStratum S d).Nonempty)
      (I : D → Ideal S)
      (_e : S ≃ₐ[k] ((d : D) → S ⧸ I d)),
      (∀ d : D,
        PrimeSpectrum.dimensionStratum S (d : ℕ) =
          PrimeSpectrum.zeroLocus (I d : Set S)) ∧
        ∀ d : D,
          ∀ m : MaximalSpectrum (S ⧸ I d), m.asIdeal.height = (d : ℕ) := sorry
/- Proof strategy: use the finite clopen stratification supplied by the
Cohen--Macaulay dimension theorem, obtain complete orthogonal idempotents,
and apply the canonical product equivalence for their quotient ideals. -/

end Algebra.CohenMacaulay
