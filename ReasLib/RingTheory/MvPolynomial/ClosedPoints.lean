/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.JacobsonSpace

@[expose] public section

/-!
# Closed points of multivariate polynomial spectra

This file concerns closed points in open subsets of spectra of finite-variable
polynomial rings and the corresponding residue field extensions.
-/

universe u

namespace MvPolynomial

/-- Every nonempty open subset of the spectrum of a finite-variable polynomial ring over a
field contains a closed point whose residue field is finite-dimensional and separable over
the coefficient field. -/
theorem exists_closedPoint_mem_open_finiteSeparableResidueField
    {k : Type u} [Field k]
    (d : ℕ)
    (W : TopologicalSpace.Opens (PrimeSpectrum (MvPolynomial (Fin d) k)))
    (hW : W ≠ ⊥) :
    ∃ (w : W) (_ : w.1 ∈ closedPoints (PrimeSpectrum (MvPolynomial (Fin d) k))),
      FiniteDimensional k w.1.asIdeal.ResidueField ∧
        Algebra.IsSeparable k w.1.asIdeal.ResidueField := sorry

end MvPolynomial
