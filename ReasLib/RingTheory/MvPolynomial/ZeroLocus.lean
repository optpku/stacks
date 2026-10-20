/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Defs.Induced

@[expose] public section

universe u v

noncomputable section

namespace MvPolynomial

variable {k : Type u} {σ : Type v} [Field k]

/-- The classical zero locus of an ideal, equipped with the topology induced by
its evaluation points in the prime spectrum of the polynomial ring. -/
abbrev ClassicalZeroLocus (I : Ideal (MvPolynomial σ k)) :=
  WithTopology (MvPolynomial.zeroLocus k I)
    (TopologicalSpace.induced
      (fun x : MvPolynomial.zeroLocus k I =>
        MvPolynomial.pointToPoint (k := k) (K := k) x.1)
      inferInstance)

namespace ClassicalZeroLocus

/-- A closed subset of a classical zero locus is the restriction of a polynomial
zero locus. -/
theorem isClosed_iff (I : Ideal (MvPolynomial σ k))
    (S : Set (ClassicalZeroLocus I)) :
    IsClosed S ↔ ∃ J : Ideal (MvPolynomial σ k),
      S = {point | point.ofTopology.val ∈ MvPolynomial.zeroLocus k J} := sorry

/-- The topological Krull dimension of a classical zero locus in finitely many
variables over an algebraically closed field equals the Krull dimension of its
quotient coordinate ring. -/
theorem topologicalKrullDim_eq_ringKrullDim
    (I : Ideal (MvPolynomial σ k)) [Finite σ] [IsAlgClosed k] :
    topologicalKrullDim (ClassicalZeroLocus I) =
      ringKrullDim (MvPolynomial σ k ⧸ I) := sorry

end ClassicalZeroLocus

end MvPolynomial
