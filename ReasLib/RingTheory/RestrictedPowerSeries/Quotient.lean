module

public import Mathlib.Topology.Algebra.Ring.Ideal
public import ReasLib.RingTheory.RestrictedPowerSeries

/-!
# Closed quotients of restricted power series

A homomorphism `φ : B →+* A` exhibits `A` as a topological `B`-algebra quotient of
a finite-variable restricted power series ring when `A` is isomorphic, via a
two-sided continuous ring equivalence commuting with `φ`, to
`RestrictedPowerSeries (Fin n) B ⧸ K` for some closed ideal `K`.
-/

@[expose] public section

universe u

namespace RingHom

variable {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [IsLinearTopology B B] [CommRing A] [TopologicalSpace A]

/-- `A` is a closed quotient of `RestrictedPowerSeries (Fin n) B` as a topological
`B`-algebra along `φ`. -/
def IsClosedQuotientOfRestrictedPowerSeries (φ : B →+* A) : Prop :=
  ∃ (n : ℕ) (K : Ideal (RestrictedPowerSeries (Fin n) B)),
    IsClosed (K : Set (RestrictedPowerSeries (Fin n) B)) ∧
      ∃ e : RestrictedPowerSeries (Fin n) B ⧸ K ≃+* A,
        Continuous e ∧ Continuous e.symm ∧
          e.toRingHom.comp
              ((Ideal.Quotient.mk K).comp
                (algebraMap B (RestrictedPowerSeries (Fin n) B))) = φ

/-- Closed-quotient form unpacks a closed ideal in a finite-variable restricted
power series ring and a two-sided continuous `RingEquiv` commuting with `φ`. -/
theorem isClosedQuotientOfRestrictedPowerSeries_iff (φ : B →+* A) :
    φ.IsClosedQuotientOfRestrictedPowerSeries ↔
      ∃ (n : ℕ) (K : Ideal (RestrictedPowerSeries (Fin n) B)),
        IsClosed (K : Set (RestrictedPowerSeries (Fin n) B)) ∧
          ∃ e : RestrictedPowerSeries (Fin n) B ⧸ K ≃+* A,
            Continuous e ∧ Continuous e.symm ∧
              e.toRingHom.comp
                  ((Ideal.Quotient.mk K).comp
                    (algebraMap B (RestrictedPowerSeries (Fin n) B))) = φ :=
  Iff.rfl

namespace IsClosedQuotientOfRestrictedPowerSeries

/-- Package a closed restricted-power-series quotient together with a two-sided
continuous commuting `RingEquiv`. -/
theorem of {n : ℕ} {K : Ideal (RestrictedPowerSeries (Fin n) B)} {φ : B →+* A}
    (hK : IsClosed (K : Set (RestrictedPowerSeries (Fin n) B)))
    (e : RestrictedPowerSeries (Fin n) B ⧸ K ≃+* A) (he : Continuous e)
    (he_symm : Continuous e.symm)
    (hcomm : e.toRingHom.comp
        ((Ideal.Quotient.mk K).comp
          (algebraMap B (RestrictedPowerSeries (Fin n) B))) = φ) :
    φ.IsClosedQuotientOfRestrictedPowerSeries :=
  ⟨n, K, hK, e, he, he_symm, hcomm⟩

/-- A closed restricted-power-series quotient yields `n`, a closed ideal `K`, and
a two-sided continuous `RingEquiv` commuting with `φ`. -/
theorem spec {φ : B →+* A} (h : φ.IsClosedQuotientOfRestrictedPowerSeries) :
    ∃ (n : ℕ) (K : Ideal (RestrictedPowerSeries (Fin n) B)),
      IsClosed (K : Set (RestrictedPowerSeries (Fin n) B)) ∧
        ∃ e : RestrictedPowerSeries (Fin n) B ⧸ K ≃+* A,
          Continuous e ∧ Continuous e.symm ∧
            e.toRingHom.comp
                ((Ideal.Quotient.mk K).comp
                  (algebraMap B (RestrictedPowerSeries (Fin n) B))) = φ :=
  h

end IsClosedQuotientOfRestrictedPowerSeries

end RingHom
