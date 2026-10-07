module

public import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Module.Torsion.Stability
public import ReasLib.RingTheory.Algebra.Quotient.PrincipalPower
public import ReasLib.RingTheory.Smooth.Factorization.PrincipalPowerLift
public import ReasLib.RingTheory.Smooth.Standard.Element.Selected

/-!
# Principal-annihilator power lifts

This leaf specializes principal-power lifts to a factorization modulo the
eighth power of a principal parameter.
-/

@[expose] public section

universe u v w x

namespace AlgHom.Factorisation.Finite.PrincipalPowerLift

variable {R : Type u} {A : Type v} {Cbar : Type w} {Λ : Type x}
variable [CommRing R] [CommRing A] [CommRing Cbar] [CommRing Λ]
variable [Algebra R A] [Algebra R Λ]

/-- A finite-presentation factorisation of the reduction modulo `π ^ 8`
produces a principal-power lift under the principal-annihilator hypotheses. -/
theorem nonempty_of_principalAnnihilator
    (π : R) [IsNoetherianRing R]
    [Algebra (R ⧸ principalPowerIdeal π 8) Cbar]
    [Algebra.FinitePresentation (R ⧸ principalPowerIdeal π 8) Cbar]
    (fA : A →ₐ[R] Λ)
    (hAnnR : Module.IsTorsionStable R R π)
    (hAnnΛ : Module.IsTorsionStable Λ Λ (algebraMap R Λ π))
    (hπ : Algebra.IsStrictlyStandard R (algebraMap R A π))
    (reduction : AlgHom.Factorisation.Through
      (Algebra.PrincipalQuotient.map fA π 8) Cbar) :
    Nonempty (PrincipalPowerLift π 8 fA reduction.toTarget) := sorry

/-- Lemma 16.7.3 (07F0): a factorisation modulo `π ^ 8` produces a
principal-power lift smooth away from `π`. -/
@[stacks 07F0]
theorem nonempty_ofMaps
    (π : R) [IsNoetherianRing R]
    [Algebra (R ⧸ principalPowerIdeal π 8) Cbar]
    [Algebra.FinitePresentation (R ⧸ principalPowerIdeal π 8) Cbar]
    (fA : A →ₐ[R] Λ)
    (hAnnR : Module.IsTorsionStable R R π)
    (hAnnΛ : Module.IsTorsionStable Λ Λ (algebraMap R Λ π))
    (hπ : Algebra.IsStrictlyStandard R (algebraMap R A π))
    (fbar : Algebra.PrincipalQuotient R A π 8 →ₐ[R ⧸ principalPowerIdeal π 8]
      Cbar)
    (gbar : Cbar →ₐ[R ⧸ principalPowerIdeal π 8]
      Algebra.PrincipalQuotient R Λ π 8)
    (hfactor : gbar.comp fbar = Algebra.PrincipalQuotient.map fA π 8) :
    Nonempty (PrincipalPowerLift π 8 fA gbar) := sorry

end AlgHom.Factorisation.Finite.PrincipalPowerLift
