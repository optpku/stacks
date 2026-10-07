module

public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Henselian
public import ReasLib.RingTheory.Ideal.IdempotentLifting
import Mathlib.Tactic.CrossRefAttribute

/-!
# Criteria for henselian pairs

This leaf owns the etale-section, idempotent-lifting, and Gabber polynomial criteria for a
henselian pair. The predicates remain atomic; the source's five-way equivalence is exposed both
as a `List.TFAE` and through named binary equivalences.

@stack 09XI
-/

@[expose] public section

open Polynomial
open scoped Polynomial

universe u

namespace Ideal

variable {A : Type u} [CommRing A]

/-- Every section modulo `I` of an etale `A`-algebra lifts to an `A`-algebra map to `A`. -/
@[stacks 09XI "etale-section lifting criterion"]
def HasEtaleLiftProperty (I : Ideal A) : Prop :=
  ∀ ⦃A' : Type u⦄ [CommRing A'] [Algebra A A'] [Algebra.Etale A A'],
    Function.Surjective fun τ : A' →ₐ[A] A ↦ (Ideal.Quotient.mkₐ A I).comp τ

/-- A monic polynomial whose reduction modulo `I` is `X ^ n * (X - 1)` for some `n > 0`. -/
@[stacks 09XI "Gabber test polynomial"]
def IsGabberHenselPolynomial (I : Ideal A) (f : A[X]) : Prop :=
  ∃ n : ℕ, 0 < n ∧ f.Monic ∧
    f.map (Ideal.Quotient.mk I) = X ^ n * (X - 1)

/-- The Jacobson condition together with existence of a root in `1 + I` for every Gabber test
polynomial. -/
@[stacks 09XI "Gabber root criterion"]
def SatisfiesGabberRootCriterion (I : Ideal A) : Prop :=
  I ≤ Ring.jacobson A ∧
    ∀ ⦃f : A[X]⦄, I.IsGabberHenselPolynomial f → ∃ i : I, f.IsRoot (1 + ↑i)

namespace HenselianPairCriteria

/-- Lemma 15.11.6: henselianity, etale-section lifting, finite- and integral-algebra idempotent
lifting, and Gabber's root criterion are equivalent. -/
@[stacks 09XI "Lemma 15.11.6"]
theorem tfae (I : Ideal A) :
    List.TFAE
      [ HenselianRing A I
      , I.HasEtaleLiftProperty
      , Ideal.HasFiniteAlgebraIdempotentLifting.{u, u} (A := A) I
      , Ideal.HasIntegralAlgebraIdempotentLifting.{u, u} (A := A) I
      , I.SatisfiesGabberRootCriterion
      ] := sorry

/-- Henselianity is equivalent to lifting etale sections modulo the ideal. -/
@[stacks 09XI "henselianity and etale-section lifting"]
theorem henselian_iff_etaleLift (I : Ideal A) :
    HenselianRing A I ↔ I.HasEtaleLiftProperty := sorry

/-- Henselianity is equivalent to idempotent lifting for finite algebras. -/
@[stacks 09XI "henselianity and finite-algebra idempotent lifting"]
theorem henselian_iff_finiteIdempotentLifting (I : Ideal A) :
    HenselianRing A I ↔
      Ideal.HasFiniteAlgebraIdempotentLifting.{u, u} (A := A) I := sorry

/-- Henselianity is equivalent to idempotent lifting for integral algebras. -/
@[stacks 09XI "henselianity and integral-algebra idempotent lifting"]
theorem henselian_iff_integralIdempotentLifting (I : Ideal A) :
    HenselianRing A I ↔
      Ideal.HasIntegralAlgebraIdempotentLifting.{u, u} (A := A) I := sorry

/-- Henselianity is equivalent to Gabber's Jacobson-plus-root criterion. -/
@[stacks 09XI "henselianity and the Gabber root criterion"]
theorem henselian_iff_gabber (I : Ideal A) :
    HenselianRing A I ↔ I.SatisfiesGabberRootCriterion := sorry

/-- A henselian pair has bijective reduction on idempotents for the identity algebra. -/
@[stacks 09XI "idempotents modulo a henselian ideal"]
theorem idempotentMap_bijective (I : Ideal A) [HenselianRing A I] :
    Function.Bijective (Ideal.Quotient.mk I).idempotentMap := sorry

end HenselianPairCriteria

namespace SatisfiesGabberRootCriterion

/-- Gabber's root criterion implies that the pair is henselian. -/
@[stacks 09XI "Gabber criterion implies henselianity"]
theorem henselianRing {I : Ideal A} (hI : I.SatisfiesGabberRootCriterion) :
    HenselianRing A I := sorry

/-- The root in `1 + I` supplied by Gabber's criterion is unique. -/
@[stacks 09XI "uniqueness in the Gabber root criterion"]
theorem existsUnique {I : Ideal A} (hI : I.SatisfiesGabberRootCriterion)
    {f : A[X]} (hf : I.IsGabberHenselPolynomial f) :
    ∃! i : I, f.IsRoot (1 + ↑i) := sorry

end SatisfiesGabberRootCriterion

end Ideal
