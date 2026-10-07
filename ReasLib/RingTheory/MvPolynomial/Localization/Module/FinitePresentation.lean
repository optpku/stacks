module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Module.FinitePresentation.RingEquiv
public import ReasLib.RingTheory.MvPolynomial.Localization.Module

/-!
# Finite Presentation on Coefficient-Localized Polynomial Charts

This leaf transfers finite presentation of a polynomial module to the
coefficient-localized polynomial chart.  The result keeps the normalized
`awayCModule` action explicit, so it can be used without choosing a global
scalar presentation for the localized carrier.

@stack 051T
-/

@[expose] public section

universe u v w

namespace MvPolynomial.Localization

open scoped MvPolynomial.Localization

variable {σ : Type u} {A : Type v} [CommRing A]
variable {N : Type w} [AddCommGroup N] [Module (MvPolynomial σ A) N]

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Tag `051T`: finite presentation of a polynomial module persists after
localizing coefficients away from `f`.  In the
`MvPolynomial.Localization` scope it is the finite-presentation instance for
the normalized coefficient chart. -/
@[stacks 051T "finite presentation on coefficient polynomial localization"]
theorem finitePresentation_awayC (f : A)
    [Module.FinitePresentation (MvPolynomial σ A) N] :
    Module.FinitePresentation (MvPolynomial σ (Localization.Away f))
      (LocalizedModule.Away (MvPolynomial.C (σ := σ) f) N) := sorry

end MvPolynomial.Localization

/-! In the normalized coefficient-localization scope, finite presentation is
inferred from the original polynomial-module finite-presentation instance. -/
scoped[MvPolynomial.Localization] attribute [instance 100]
  MvPolynomial.Localization.finitePresentation_awayC

section

open scoped MvPolynomial.Localization

variable {σ : Type u} {A : Type v} [CommRing A]
variable {N : Type w} [AddCommGroup N] [Module (MvPolynomial σ A) N]
variable (f : A) [Module.FinitePresentation (MvPolynomial σ A) N]

attribute [local instance] MvPolynomial.algebraMvPolynomial

#synth Module.FinitePresentation (MvPolynomial σ (Localization.Away f))
  (LocalizedModule.Away (MvPolynomial.C (σ := σ) f) N)

end
