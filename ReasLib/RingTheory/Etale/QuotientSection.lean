/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import ReasLib.RingTheory.Ideal.IdempotentLifting
import Mathlib.Tactic.CrossRefAttribute

/-!
# Product decompositions from etale quotient sections

An etale algebra map to `A / I` splits the reduction of the etale algebra. Passing to the
integral closure gives a corresponding quotient factor, and integral-algebra idempotent lifting
promotes that factor to a product decomposition before reduction.

@stack 0EM1
@stack 0EM3
@stack 0EM4
-/

@[expose] public section

universe u v

namespace Algebra.Etale

section QuotientSection

variable {A : Type u} {A' : Type v} [CommRing A] [CommRing A'] [Algebra A A']
variable (I : Ideal A)

local notation "Abar" => A ⧸ I
local notation "Q" => A' ⧸ Ideal.map (algebraMap A A') I
local notation "B'" => integralClosure A A'
local notation "IB'" => Ideal.map (algebraMap A B') I

/-- An etale `A`-algebra with an `A`-algebra map to `A / I` has a quotient reduction whose first
product factor is `A / I`.

The section and the resulting idempotent remain explicit existential data; this theorem does not
choose a global splitting. -/
@[stacks 0EM1 "quotient product decomposition from an etale section"]
theorem exists_quotientProductEquiv_of_section [Algebra.Etale A A']
    (sectionMap : A' →ₐ[A] Abar) :
    ∃ e : Q,
      IsIdempotentElem e ∧
        ∃ productEquiv :
            Q ≃ₐ[Abar] (Abar × (Q ⧸ Ideal.span ({1 - e} : Set Q))),
          ∀ x : Abar, (productEquiv (algebraMap Abar Q x)).1 = x := sorry

/-- The reduction of the integral closure associated to an etale quotient section has a
canonical quotient factor isomorphic to `A / I`.

This fine-grained factor statement avoids requiring clients to unpack a full product
decomposition when they only need the base factor. -/
@[stacks 0EM3 "integral-closure quotient factor from an etale section"]
theorem exists_integralClosureQuotientEquiv_of_section [Algebra.Etale A A']
    (sectionMap : A' →ₐ[A] Abar) :
    ∃ e : B' ⧸ IB',
      IsIdempotentElem e ∧
        ∃ firstFactor :
            ((B' ⧸ IB') ⧸ Ideal.span ({e} : Set (B' ⧸ IB'))) ≃ₐ[Abar] Abar,
          ∀ x : Abar,
            firstFactor
                (Ideal.Quotient.mk (Ideal.span ({e} : Set (B' ⧸ IB')))
                  (algebraMap Abar (B' ⧸ IB') x)) = x := sorry

end QuotientSection

end Algebra.Etale

namespace Ideal.HasIntegralAlgebraIdempotentLifting

section IntegralClosure

variable {A : Type u} {A' : Type (max u v)} [CommRing A] [CommRing A'] [Algebra A A']
variable (I : Ideal A)

local notation "B'" => integralClosure A A'

/-- Integral-algebra idempotent lifting turns an etale quotient section into an `A`-algebra
product decomposition of the integral closure.

The lifting hypothesis is an explicit proof for the selected ideal rather than a typeclass, so
the theorem also applies when henselianity is available only through a chosen criterion. -/
@[stacks 0EM4, stacks 0EM2
  "integral-closure product decomposition from an etale quotient section"]
theorem exists_integralClosureProductEquiv_of_etaleSection
    (hI : Ideal.HasIntegralAlgebraIdempotentLifting.{u, v} (A := A) I)
    [Algebra.Etale A A'] (sectionMap : A' →ₐ[A] A ⧸ I) :
    ∃ (e : B') (_he : IsIdempotentElem e)
      (productEquiv :
        B' ≃ₐ[A]
          ((B' ⧸ Ideal.span ({e} : Set B')) ×
            (B' ⧸ Ideal.span ({1 - e} : Set B')))),
      ∀ x : B',
        productEquiv x =
          (Ideal.Quotient.mk (Ideal.span ({e} : Set B')) x,
            Ideal.Quotient.mk (Ideal.span ({1 - e} : Set B')) x) := sorry

end IntegralClosure

end Ideal.HasIntegralAlgebraIdempotentLifting
