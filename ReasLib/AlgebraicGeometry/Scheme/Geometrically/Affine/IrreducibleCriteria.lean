/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Spec.Topology

/-!
# Affine Criteria for Geometric Irreducibility

This leaf owns the ring-level presentations of geometric irreducibility for an
affine algebra over a field.  The source item's four-way `TFAE` is represented
by atomic equivalences: finite separable extensions, an arbitrary chosen
separable closure, and an arbitrary chosen algebraic closure.  The canonical
closure names below are convenience specializations of those class-parametric
owners.
-/

@[expose] public section

open AlgebraicGeometry CommRingCat
open scoped TensorProduct

universe u v

namespace AlgebraicGeometry.SchemeOverField

namespace GeometricallyIrreducible.Spectrum

section

variable {k R : Type u} [Field k] [CommRing R] [Algebra k R]

/-- Lemma 10.47.3 (Tag 037K), clauses `(1) ↔ (2)`: geometric irreducibility of an affine
`k`-algebra can be tested after every finite separable extension of `k`. -/
@[stacks 037K]
theorem iff_finiteSeparableBaseChange :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap k R))) ↔
      ∀ (K : Type u) [Field K] [Algebra k K]
        [FiniteDimensional k K] [Algebra.IsSeparable k K],
        IrreducibleSpace (PrimeSpectrum (R ⊗[k] K)) := sorry

/-- Class-parametric form of the separable-closure criterion.  Any chosen `ksep` carrying
`IsSepClosure k ksep` may be used; this avoids making the canonical quotient
`SeparableClosure k` part of the reusable statement. -/
@[stacks 037K "chosen separable closure criterion"]
theorem iff_of_isSepClosure
    {ksep : Type v} [Field ksep] [Algebra k ksep] [IsSepClosure k ksep] :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap k R))) ↔
      IrreducibleSpace (PrimeSpectrum (R ⊗[k] ksep)) := sorry

/-- Lemma 10.47.3 (Tag 037K), clause `(3)`: the canonical separable closure is one sufficient
base change for testing geometric irreducibility. -/
@[stacks 037K]
theorem iff_separableClosure :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap k R))) ↔
      IrreducibleSpace (PrimeSpectrum (R ⊗[k] SeparableClosure k)) := sorry

/-- Class-parametric form of the algebraic-closure criterion. -/
@[stacks 037K "chosen algebraic closure criterion"]
theorem iff_of_isAlgClosure
    {kbar : Type v} [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar] :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap k R))) ↔
      IrreducibleSpace (PrimeSpectrum (R ⊗[k] kbar)) := sorry

/-- Lemma 10.47.3 (Tag 037K), clause `(4)`: the canonical algebraic closure is one sufficient
base change for testing geometric irreducibility. -/
@[stacks 037K]
theorem iff_algebraicClosure :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap k R))) ↔
      IrreducibleSpace (PrimeSpectrum (R ⊗[k] AlgebraicClosure k)) := sorry

/-- Lemma 10.47.5 (Tag 037M): over a separably closed field, geometric irreducibility of an
affine algebra is exactly irreducibility of its prime spectrum. -/
@[stacks 037M]
theorem iff_of_isSepClosed
    [IsSepClosed k] :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap k R))) ↔
      IrreducibleSpace (PrimeSpectrum R) := sorry

end

end GeometricallyIrreducible.Spectrum

end AlgebraicGeometry.SchemeOverField
