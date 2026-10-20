module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Module.LocalizedModule.Equiv
public import ReasLib.RingTheory.MvPolynomial.Localization.Module

/-!
# Equivalences of Coefficient-Localized Polynomial Modules

This leaf transports a bijective localized polynomial-module map from the
direct localization away from `MvPolynomial.C f` to the normalized coefficient
chart `MvPolynomial σ (Localization.Away f)`.  The normalization is available
for every variable type and does not depend on finite presentation data.

@stack 051T
-/

@[expose] public section

universe u v w x

namespace MvPolynomial.Localization

open scoped MvPolynomial.Localization

variable {σ : Type u} {A : Type v} [CommRing A]
variable {M : Type w} [AddCommMonoid M] [Module (MvPolynomial σ A) M]
variable {N : Type x} [AddCommMonoid N] [Module (MvPolynomial σ A) N]

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Tag `051T`: a bijective coefficient-away localized polynomial-module map,
viewed through the normalized coefficient chart.  Its scalar actions are
available after opening the controlled `MvPolynomial.Localization` scope. -/
@[stacks 051T "coefficient polynomial localized map equivalence"]
noncomputable def awayCMapEquiv (f : A) (φ : M →ₗ[MvPolynomial σ A] N)
    (hφ : Function.Bijective
      (LocalizedModule.map (Submonoid.powers (MvPolynomial.C (σ := σ) f)) φ)) :
    LocalizedModule.Away (MvPolynomial.C (σ := σ) f) M ≃ₗ[
      MvPolynomial σ (Localization.Away f)]
      LocalizedModule.Away (MvPolynomial.C (σ := σ) f) N :=
  (LinearEquiv.restrictScalars (MvPolynomial σ A)
      (LocalizedModule.mapEquivOfBijective
        (Submonoid.powers (MvPolynomial.C (σ := σ) f)) φ hφ)
    ).extendScalarsOfIsLocalization
      (Submonoid.powers (MvPolynomial.C (σ := σ) f))
      (MvPolynomial σ (Localization.Away f))

/-- The normalized equivalence induced by a bijective localized map has the
canonical localized map as its underlying function. -/
@[simp, stacks 051T "coefficient polynomial localized map equivalence application"]
theorem awayCMapEquiv_apply (f : A) (φ : M →ₗ[MvPolynomial σ A] N)
    (hφ : Function.Bijective
      (LocalizedModule.map (Submonoid.powers (MvPolynomial.C (σ := σ) f)) φ))
    (x : LocalizedModule.Away (MvPolynomial.C (σ := σ) f) M) :
    awayCMapEquiv f φ hφ x =
      LocalizedModule.map (Submonoid.powers (MvPolynomial.C (σ := σ) f)) φ x := sorry

end MvPolynomial.Localization
