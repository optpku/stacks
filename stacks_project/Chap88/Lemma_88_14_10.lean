module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.AdicCompletion.AtPrime
public import stacks_project.Chap87.Remark_87_28_1_Universal_property_restricted_power_series_RestrictedPowerSeries
public import stacks_project.Chap88.Lemma_88_14_10_Instances
public import stacks_project.Chap88.Lemma_88_14_3_RigClosed

/-!
# Completions of localizations at rig-closed primes of restricted power series
-/

@[expose] public section

universe u

namespace RestrictedPowerSeries

variable {A : Type u} [CommRing A] [TopologicalSpace A]
  [TopologicalRing.IsAdicRing A] [IsNoetherianRing A]

/-- Lemma 88.14.10: if `A` is a Noetherian adic topological ring, `q` is a
rig-closed prime of `RestrictedPowerSeries (Fin n) A`, and
`q.comap (algebraMap A (RestrictedPowerSeries (Fin n) A))` is also rig-closed,
then the completed local map of `ofPolynomial` is an isomorphism of completed
local rings. -/
@[stacks 0GGH]
noncomputable def completedLocalRingEquiv (n : ℕ)
    (q : Ideal (RestrictedPowerSeries (Fin n) A))
    [q.IsRigClosed]
    [(q.comap (algebraMap A (RestrictedPowerSeries (Fin n) A))).IsRigClosed] :
    PrimeSpectrum.CompletedLocalRing
      (PrimeSpectrum.comap
        (ofPolynomial : MvPolynomial (Fin n) A →ₐ[A]
          RestrictedPowerSeries (Fin n) A).toRingHom
        ⟨q, inferInstance⟩) ≃+*
      PrimeSpectrum.CompletedLocalRing ⟨q, inferInstance⟩ :=
  RingEquiv.ofBijective
    (RingHom.completedLocalMap
      (ofPolynomial : MvPolynomial (Fin n) A →ₐ[A]
        RestrictedPowerSeries (Fin n) A).toRingHom
      ⟨q, inferInstance⟩) sorry

/-- The underlying homomorphism of `completedLocalRingEquiv` is the canonical
completed local map of `ofPolynomial`. -/
theorem completedLocalRingEquiv_toRingHom (n : ℕ)
    (q : Ideal (RestrictedPowerSeries (Fin n) A))
    [q.IsRigClosed]
    [(q.comap (algebraMap A (RestrictedPowerSeries (Fin n) A))).IsRigClosed] :
    (completedLocalRingEquiv n q).toRingHom =
      RingHom.completedLocalMap
        (ofPolynomial : MvPolynomial (Fin n) A →ₐ[A]
          RestrictedPowerSeries (Fin n) A).toRingHom
        ⟨q, inferInstance⟩ :=
  sorry

end RestrictedPowerSeries
