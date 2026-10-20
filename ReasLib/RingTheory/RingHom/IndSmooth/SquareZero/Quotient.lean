module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ReasLib.Algebra.AlgHom.Factorisation.SmoothQuotient
public import ReasLib.RingTheory.RingHom.IndSmooth.Basic

/-!
# Smooth quotient factorizations across square-zero ideals

This leaf isolates the quotient-factorization step for ind-smooth targets
modulo a square-zero ideal.
-/

@[expose] public section

universe u v w

namespace AlgHom.QuotientFactorisation.Smooth

variable {R : Type u} {A : Type v} {Λ : Type w}
variable [CommRing R] [CommRing A] [CommRing Λ]
variable [Algebra R A] [Algebra R Λ]

/-- Lemma 16.5.1 (tag 07CK): a finite-presentation map into a target that is ind-smooth modulo a
square-zero ideal factors through a finitely generated quotient of a smooth algebra. -/
@[stacks 07CK]
theorem nonempty_of_squareZero
    (I : Ideal R) [Algebra.FinitePresentation R A] (hI : I ^ 2 = ⊥)
    (hquot :
      (algebraMap (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))).IndSmooth)
    (φ : A →ₐ[R] Λ) :
    Nonempty (AlgHom.QuotientFactorisation.Smooth I φ) := sorry

end AlgHom.QuotientFactorisation.Smooth
