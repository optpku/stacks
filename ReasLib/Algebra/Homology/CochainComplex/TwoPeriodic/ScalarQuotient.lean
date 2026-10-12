/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Regular.SMul
public import Mathlib.Algebra.Ring.NonZeroDivisors
public import Mathlib.RingTheory.QuotSMulTop
public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Quotient

/-!
# Scalar Two-Periodic Complexes on Quotient Modules

This file specializes the quotient-by-composite-range construction to scalar multiplication
endomorphisms.
-/

@[expose] public section

open CategoryTheory
open scoped Pointwise nonZeroDivisors

universe u v

namespace CategoryTheory.TwoPeriodicEndomorphism

variable {A : Type u} [CommRing A]

/-- The range of multiplication first by `b` and then by `a` is `(a * b) • ⊤`. -/
theorem scalarCompRange_eq_smulTop (M : Type v) [AddCommGroup M] [Module A M]
    (a b : A) :
    ((LinearMap.lsmul A M a).comp (LinearMap.lsmul A M b)).range =
      (a * b) • (⊤ : Submodule A M) := sorry

/-- Scalar multiplication by `a` and `b` has the same composite range in either order. -/
theorem scalarCompRange_comm (M : Type v) [AddCommGroup M] [Module A M]
    (a b : A) :
    ((LinearMap.lsmul A M a).comp (LinearMap.lsmul A M b)).range =
      ((LinearMap.lsmul A M b).comp (LinearMap.lsmul A M a)).range := sorry

/-- The two-periodic complex on the quotient of `M` by multiplication by `a * b`, with
differentials induced by multiplication by `a` and `b`. -/
def ofScalarQuotient (M : Type v) [AddCommGroup M] [Module A M]
    (a b : A) : TwoPeriodicEndomorphism (ModuleCat A) :=
  ofQuotientComp (LinearMap.lsmul A M a) (LinearMap.lsmul A M b)
    (scalarCompRange_comm M a b)

/-- The object underlying `ofScalarQuotient M a b` is `M ⧸ (a * b) • ⊤`. -/
theorem ofScalarQuotient_X (M : Type v) [AddCommGroup M] [Module A M]
    (a b : A) :
    (ofScalarQuotient M a b).X = ModuleCat.of A (QuotSMulTop (a * b) M) := sorry

/-- On quotient representatives, the degree-zero differential is multiplication by `a`. -/
theorem ofScalarQuotient_d₀_apply_mk (M : Type v) [AddCommGroup M] [Module A M]
    (a b : A) (x : M) :
    (ofScalarQuotient M a b).d₀.hom (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (a • x) := sorry

/-- On quotient representatives, the degree-one differential is multiplication by `b`. -/
theorem ofScalarQuotient_d₁_apply_mk (M : Type v) [AddCommGroup M] [Module A M]
    (a b : A) (x : M) :
    (ofScalarQuotient M a b).d₁.hom (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (b • x) := sorry

/-- The scalar quotient complex has a finite-length underlying module in the local
Noetherian dimension-one setting. -/
theorem ofScalarQuotient_isFiniteLength
    [IsLocalRing A] [IsNoetherianRing A]
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (a b : A) (ha : IsSMulRegular M a) (hb : IsSMulRegular M b)
    (hdim : Module.supportDim A M = 1) :
    IsFiniteLength A (ofScalarQuotient M a b).X := sorry

/-- Regularity of both scalars makes the scalar quotient complex acyclic. -/
theorem ofScalarQuotient_acyclic_of_regular
    (M : Type v) [AddCommGroup M] [Module A M]
    (a b : A) (ha : IsSMulRegular M a) (hb : IsSMulRegular M b) :
    (ofScalarQuotient M a b).toCochainComplex.Acyclic := sorry

/-- A quotient by the product of two regular scalars has finite length when the module is
finite of support dimension one over a Noetherian local ring. -/
theorem scalarQuotient_length_lt_top
    [IsLocalRing A] [IsNoetherianRing A]
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (a b : A) (ha : IsSMulRegular M a) (hb : IsSMulRegular M b)
    (hdim : Module.supportDim A M = 1) :
    Module.length A (QuotSMulTop (a * b) M) < ⊤ := sorry

/-- Multiplication by two regular scalars on their product quotient gives an acyclic
two-periodic complex in the finite dimension-one local setting. -/
theorem scalarQuotient_acyclic
    [IsLocalRing A] [IsNoetherianRing A]
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (a b : A) (ha : IsSMulRegular M a) (hb : IsSMulRegular M b)
    (hdim : Module.supportDim A M = 1) :
    (ofScalarQuotient M a b).toCochainComplex.Acyclic := sorry

/-- The quotient of a one-dimensional Noetherian local ring by the product of two
nonzerodivisors has finite length. -/
theorem scalarQuotient_self_length_lt_top
    [IsLocalRing A] [IsNoetherianRing A]
    (a b : A) (ha : a ∈ A⁰) (hb : b ∈ A⁰) (hdim : ringKrullDim A = 1) :
    Module.length A (QuotSMulTop (a * b) A) < ⊤ := sorry

/-- Multiplication by two nonzerodivisors on their product quotient gives an acyclic
two-periodic complex for a one-dimensional Noetherian local ring. -/
theorem scalarQuotient_self_acyclic
    [IsLocalRing A] [IsNoetherianRing A]
    (a b : A) (ha : a ∈ A⁰) (hb : b ∈ A⁰) (hdim : ringKrullDim A = 1) :
    (ofScalarQuotient A a b).toCochainComplex.Acyclic := sorry

/-- The self-module scalar quotient complex has finite length under the one-dimensional
Noetherian local ring hypotheses. -/
theorem scalarQuotientSelf_isFiniteLength
    [IsLocalRing A] [IsNoetherianRing A]
    (a b : A) (ha : a ∈ A⁰) (hb : b ∈ A⁰) (hdim : ringKrullDim A = 1) :
    IsFiniteLength A (ofScalarQuotient A a b).X := sorry

end CategoryTheory.TwoPeriodicEndomorphism
