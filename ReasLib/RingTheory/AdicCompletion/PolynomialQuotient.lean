module

public import Mathlib.Topology.Defs.Induced
public import ReasLib.RingTheory.Topology.Adic.Basic
public import ReasLib.RingTheory.AdicCompletion.Polynomial

/-!
# Closed quotients of polynomial completions

A homomorphism `φ : A →+* B` exhibits `B` as a topological `A`-algebra quotient of
a finite-variable polynomial completion when `B` is isomorphic, via a two-sided
continuous ring equivalence commuting with `φ`, to
`IAdicRestrictedPowerSeries (Fin n) I ⧸ K` for some ideal of definition `I` of `A`
and some ideal `K` closed in the inverse-limit topology.
-/

@[expose] public section

universe u

open TopologicalRing
open TopologicalRing.Ideal

namespace RingHom

variable {A B : Type u}
variable [CommRing A] [TopologicalSpace A]
variable [CommRing B] [TopologicalSpace B]

/-- `B` is a closed quotient of `IAdicRestrictedPowerSeries (Fin n) I` as a
topological `A`-algebra along `φ`, for some ideal of definition `I` of `A`. -/
def IsClosedQuotientOfPolynomialCompletion (φ : A →+* B) : Prop :=
  ∃ (I : Ideal A), IsIdealOfDefinition I ∧
    ∃ (n : ℕ) (K : Ideal (IAdicRestrictedPowerSeries (Fin n) I)),
      @IsClosed (IAdicRestrictedPowerSeries (Fin n) I)
        (IAdicRestrictedPowerSeries.limitTopology (Fin n) I)
        (K : Set (IAdicRestrictedPowerSeries (Fin n) I)) ∧
        ∃ e : IAdicRestrictedPowerSeries (Fin n) I ⧸ K ≃+* B,
          @Continuous _ _
            (TopologicalSpace.coinduced (Ideal.Quotient.mk K)
              (IAdicRestrictedPowerSeries.limitTopology (Fin n) I)) _ e ∧
            @Continuous _ _ _
              (TopologicalSpace.coinduced (Ideal.Quotient.mk K)
                (IAdicRestrictedPowerSeries.limitTopology (Fin n) I)) e.symm ∧
              e.toRingHom.comp
                  ((Ideal.Quotient.mk K).comp
                    (algebraMap A (IAdicRestrictedPowerSeries (Fin n) I))) = φ

/-- Closed-quotient form unpacks a closed ideal in a finite-variable polynomial
completion and a two-sided continuous `RingEquiv` commuting with `φ`. -/
theorem isClosedQuotientOfPolynomialCompletion_iff (φ : A →+* B) :
    φ.IsClosedQuotientOfPolynomialCompletion ↔
      ∃ (I : Ideal A), IsIdealOfDefinition I ∧
        ∃ (n : ℕ) (K : Ideal (IAdicRestrictedPowerSeries (Fin n) I)),
          @IsClosed (IAdicRestrictedPowerSeries (Fin n) I)
            (IAdicRestrictedPowerSeries.limitTopology (Fin n) I)
            (K : Set (IAdicRestrictedPowerSeries (Fin n) I)) ∧
            ∃ e : IAdicRestrictedPowerSeries (Fin n) I ⧸ K ≃+* B,
              @Continuous _ _
                (TopologicalSpace.coinduced (Ideal.Quotient.mk K)
                  (IAdicRestrictedPowerSeries.limitTopology (Fin n) I)) _ e ∧
                @Continuous _ _ _
                  (TopologicalSpace.coinduced (Ideal.Quotient.mk K)
                    (IAdicRestrictedPowerSeries.limitTopology (Fin n) I)) e.symm ∧
                  e.toRingHom.comp
                      ((Ideal.Quotient.mk K).comp
                        (algebraMap A (IAdicRestrictedPowerSeries (Fin n) I))) =
                    φ :=
  Iff.rfl

namespace IsClosedQuotientOfPolynomialCompletion

/-- A closed ideal and a two-sided continuous ring equivalence commuting with
the coefficient homomorphism exhibit a closed polynomial-completion quotient. -/
theorem of {I : Ideal A} {n : ℕ} {K : Ideal (IAdicRestrictedPowerSeries (Fin n) I)}
    {φ : A →+* B} (hI : IsIdealOfDefinition I)
    (hK : @IsClosed (IAdicRestrictedPowerSeries (Fin n) I)
      (IAdicRestrictedPowerSeries.limitTopology (Fin n) I)
      (K : Set (IAdicRestrictedPowerSeries (Fin n) I)))
    (e : IAdicRestrictedPowerSeries (Fin n) I ⧸ K ≃+* B)
    (he : @Continuous _ _
      (TopologicalSpace.coinduced (Ideal.Quotient.mk K)
        (IAdicRestrictedPowerSeries.limitTopology (Fin n) I)) _ e)
    (he_symm : @Continuous _ _ _
      (TopologicalSpace.coinduced (Ideal.Quotient.mk K)
        (IAdicRestrictedPowerSeries.limitTopology (Fin n) I)) e.symm)
    (hcomm : e.toRingHom.comp
        ((Ideal.Quotient.mk K).comp
          (algebraMap A (IAdicRestrictedPowerSeries (Fin n) I))) = φ) :
    φ.IsClosedQuotientOfPolynomialCompletion :=
  ⟨I, hI, n, K, hK, e, he, he_symm, hcomm⟩

/-- A closed polynomial-completion quotient yields an ideal of definition `I`, a
closed ideal `K`, and a two-sided continuous `RingEquiv` commuting with `φ`. -/
theorem spec {φ : A →+* B} (h : φ.IsClosedQuotientOfPolynomialCompletion) :
    ∃ (I : Ideal A), IsIdealOfDefinition I ∧
      ∃ (n : ℕ) (K : Ideal (IAdicRestrictedPowerSeries (Fin n) I)),
        @IsClosed (IAdicRestrictedPowerSeries (Fin n) I)
          (IAdicRestrictedPowerSeries.limitTopology (Fin n) I)
          (K : Set (IAdicRestrictedPowerSeries (Fin n) I)) ∧
          ∃ e : IAdicRestrictedPowerSeries (Fin n) I ⧸ K ≃+* B,
            @Continuous _ _
              (TopologicalSpace.coinduced (Ideal.Quotient.mk K)
                (IAdicRestrictedPowerSeries.limitTopology (Fin n) I)) _ e ∧
              @Continuous _ _ _
                (TopologicalSpace.coinduced (Ideal.Quotient.mk K)
                  (IAdicRestrictedPowerSeries.limitTopology (Fin n) I)) e.symm ∧
                e.toRingHom.comp
                    ((Ideal.Quotient.mk K).comp
                      (algebraMap A (IAdicRestrictedPowerSeries (Fin n) I))) =
                  φ :=
  h

end IsClosedQuotientOfPolynomialCompletion

end RingHom
