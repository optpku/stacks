module

public import ReasLib.RingTheory.RestrictedPowerSeries.Adic
public import ReasLib.RingTheory.Ideal.RigClosed
public import ReasLib.RingTheory.AdicCompletion.AtPrime

/-!
# Completed local maps at rig-closed primes of restricted power series
-/

@[expose] public section

universe u

namespace RestrictedPowerSeries

variable {A : Type u} [CommRing A] [TopologicalSpace A]
  [TopologicalRing.IsAdicRing A] [IsNoetherianRing A]

/-- For a Noetherian adic topological ring, the canonical map from polynomials
to restricted power series induces a bijection on completed local rings at a
rig-closed prime whose contraction to the coefficient ring is rig-closed. -/
theorem completedLocalMap_bijective (n : ℕ)
    (q : Ideal (RestrictedPowerSeries (Fin n) A))
    [q.IsRigClosed]
    [(q.comap (algebraMap A (RestrictedPowerSeries (Fin n) A))).IsRigClosed] :
    Function.Bijective
      (RingHom.completedLocalMap
        (ofPolynomial : MvPolynomial (Fin n) A →ₐ[A]
          RestrictedPowerSeries (Fin n) A).toRingHom
        ⟨q, inferInstance⟩) :=
  sorry

end RestrictedPowerSeries
