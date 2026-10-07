module

public import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Module.Torsion.Stability
public import ReasLib.RingTheory.Algebra.Quotient.PrincipalPower
public import ReasLib.RingTheory.Smooth.Factorization.RightSingularControl
public import ReasLib.RingTheory.Smooth.Standard.Element.Selected

/-!
# Principal-annihilator right singular control

This leaf specializes finite common factorizations to compatible maps modulo
the fourth power of a principal parameter.
-/

@[expose] public section

universe u v w x

namespace AlgHom.CommonFactorisation.Finite.RightSingularControl

variable {R : Type u} {A : Type v} {D : Type w} {Λ : Type x}
variable [CommRing R] [CommRing A] [CommRing D] [CommRing Λ]
variable [Algebra R A] [Algebra R D] [Algebra R Λ]

/-- A chosen compatible map modulo `π ^ 4` produces a finite common
factorisation with relative and absolute singular-ideal control. -/
theorem nonempty_of_principalAnnihilator
    (π : R) [IsNoetherianRing R] [Algebra.FinitePresentation R D]
    (fA : A →ₐ[R] Λ) (fD : D →ₐ[R] Λ)
    (hAnnR : Module.IsTorsionStable R R π)
    (hAnnΛ : Module.IsTorsionStable Λ Λ (algebraMap R Λ π))
    (hπ : Algebra.IsStrictlyStandard R (algebraMap R A π))
    (φ : Algebra.PrincipalQuotient R A π 4 →ₐ[R ⧸ principalPowerIdeal π 4]
      Algebra.PrincipalQuotient R D π 4)
    (hφ :
      (Algebra.PrincipalQuotient.map fD π 4).comp φ =
        Algebra.PrincipalQuotient.map fA π 4) :
    Nonempty (RightSingularControl fA fD) := sorry

/-- Lemma 16.7.2 (07CT): existence of a compatible map modulo `π ^ 4`
produces a common factorisation with singular-ideal control. -/
@[stacks 07CT]
theorem nonempty_of_exists
    (π : R) [IsNoetherianRing R] [Algebra.FinitePresentation R D]
    (fA : A →ₐ[R] Λ) (fD : D →ₐ[R] Λ)
    (hAnnR : Module.IsTorsionStable R R π)
    (hAnnΛ : Module.IsTorsionStable Λ Λ (algebraMap R Λ π))
    (hπ : Algebra.IsStrictlyStandard R (algebraMap R A π))
    (hφ : ∃ φ :
        Algebra.PrincipalQuotient R A π 4 →ₐ[R ⧸ principalPowerIdeal π 4]
          Algebra.PrincipalQuotient R D π 4,
      (Algebra.PrincipalQuotient.map fD π 4).comp φ =
        Algebra.PrincipalQuotient.map fA π 4) :
    Nonempty (RightSingularControl fA fD) := sorry

end AlgHom.CommonFactorisation.Finite.RightSingularControl
