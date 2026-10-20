/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.EqualDifferential
public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.ScalarQuotient

/-!
# Determinants of Scalar Two-Periodic Quotient Complexes

This file defines the determinant units of finite-length acyclic scalar quotient complexes.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped nonZeroDivisors

universe u v

namespace CategoryTheory.TwoPeriodicEndomorphism

/-- The determinant unit of the scalar quotient complex of a finite dimension-one module. -/
noncomputable def scalarQuotientDeterminant
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (a b : A) (ha : IsSMulRegular M a) (hb : IsSMulRegular M b)
    (hdim : Module.supportDim A M = 1) : (IsLocalRing.ResidueField A)ˣ :=
  (ofScalarQuotient M a b).determinant
    (ofScalarQuotient_isFiniteLength M a b ha hb hdim)
    (scalarQuotient_acyclic M a b ha hb hdim)

/-- The module-case scalar quotient determinant is the determinant of its canonical
two-periodic complex. -/
theorem scalarQuotientDeterminant_def
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (a b : A) (ha : IsSMulRegular M a) (hb : IsSMulRegular M b)
    (hdim : Module.supportDim A M = 1) :
    scalarQuotientDeterminant M a b ha hb hdim =
      (ofScalarQuotient M a b).determinant
        (ofScalarQuotient_isFiniteLength M a b ha hb hdim)
        (scalarQuotient_acyclic M a b ha hb hdim) := sorry

/-- The determinant unit of the scalar quotient complex of a one-dimensional Noetherian
local ring. -/
noncomputable def scalarQuotientSelfDeterminant
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (a b : A) (ha : a ∈ A⁰) (hb : b ∈ A⁰)
    (hdim : ringKrullDim A = 1) : (IsLocalRing.ResidueField A)ˣ :=
  (ofScalarQuotient A a b).determinant
    (scalarQuotientSelf_isFiniteLength a b ha hb hdim)
    (scalarQuotient_self_acyclic a b ha hb hdim)

/-- The ring-case scalar quotient determinant is the determinant of its canonical
two-periodic complex. -/
theorem scalarQuotientSelfDeterminant_def
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (a b : A) (ha : a ∈ A⁰) (hb : b ∈ A⁰)
    (hdim : ringKrullDim A = 1) :
    scalarQuotientSelfDeterminant a b ha hb hdim =
      (ofScalarQuotient A a b).determinant
        (scalarQuotientSelf_isFiniteLength a b ha hb hdim)
        (scalarQuotient_self_acyclic a b ha hb hdim) := sorry

/-- For a regular scalar on a finite dimension-one module, the determinant of the
associated scalar quotient complex is the parity sign of the quotient's length. -/
theorem scalarQuotientDeterminant_same
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (a : A) (ha : IsSMulRegular M a) (hdim : Module.supportDim A M = 1) :
    scalarQuotientDeterminant M a a ha ha hdim =
      (-1) ^ (Module.length A (QuotSMulTop a M)).toNat := sorry

end CategoryTheory.TwoPeriodicEndomorphism
