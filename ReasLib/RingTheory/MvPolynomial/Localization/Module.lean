module

public import ReasLib.RingTheory.MvPolynomial.Localization
public import Mathlib.RingTheory.Localization.Module

@[expose] public section

/-!
# Modules over Coefficient-Localized Multivariate Polynomial Rings

This leaf transports the canonical module structure on a localized module over
`Localization.Away (MvPolynomial.C f)` to the normalized polynomial chart
`MvPolynomial σ (Localization.Away f)`.  The resulting scalar actions are
named, rather than global instances: the localized-module carrier can have
other legitimate scalar presentations.

@stack 051T
-/

universe u v w

namespace MvPolynomial.Localization

variable {σ : Type u} {A : Type v} [CommRing A]
variable {N : Type w} [AddCommMonoid N] [Module (MvPolynomial σ A) N]

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Tag `051T`: the action of the coefficient-localized polynomial ring on
the localization of a polynomial module away from `C f`. -/
@[reducible, stacks 051T "coefficient polynomial localized module action"]
noncomputable def awayCModule (f : A) :
    Module (MvPolynomial σ (Localization.Away f))
      (LocalizedModule.Away (MvPolynomial.C (σ := σ) f) N) :=
  Module.compHom (LocalizedModule.Away (MvPolynomial.C (σ := σ) f) N)
    (awayCAlgEquiv (σ := σ) f).symm.toRingHom

/-- Tag `051T`: the `Localization.Away f`-action on a coefficient-away
localized polynomial module, induced directly by the canonical localization
map along `MvPolynomial.C`. -/
@[reducible, stacks 051T "coefficient polynomial localized base module action"]
noncomputable def awayCBaseModule (f : A) :
    Module (Localization.Away f)
      (LocalizedModule.Away (MvPolynomial.C (σ := σ) f) N) :=
  Module.compHom (LocalizedModule.Away (MvPolynomial.C (σ := σ) f) N)
    (Localization.awayMap (MvPolynomial.C (σ := σ) : A →+* MvPolynomial σ A) f)

/-- The normalized polynomial action is the direct localized polynomial action
transported along `awayCAlgEquiv`. -/
@[stacks 051T "coefficient polynomial localized module action formula"]
theorem awayCModule_smul (f : A)
    (p : MvPolynomial σ (Localization.Away f))
    (x : LocalizedModule.Away (MvPolynomial.C (σ := σ) f) N) :
    letI : Module (MvPolynomial σ (Localization.Away f))
        (LocalizedModule.Away (MvPolynomial.C (σ := σ) f) N) :=
      awayCModule (σ := σ) (N := N) f
    p • x = (awayCAlgEquiv (σ := σ) f).symm p • x := sorry

/-- The restricted coefficient-localization action is scalar multiplication by
the matching coefficient in the direct away-localization ring. -/
@[stacks 051T "coefficient polynomial localized base action formula"]
theorem awayCBaseModule_smul (f : A) (r : Localization.Away f)
    (x : LocalizedModule.Away (MvPolynomial.C (σ := σ) f) N) :
    letI : Module (Localization.Away f)
        (LocalizedModule.Away (MvPolynomial.C (σ := σ) f) N) :=
      awayCBaseModule (σ := σ) (N := N) f
    r • x = (awayCAlgEquiv (σ := σ) f).symm (MvPolynomial.C r) • x := sorry

/-- The restricted coefficient-localization action is the canonical away-map
action through `Localization.Away (MvPolynomial.C f)`. -/
@[stacks 051T "coefficient polynomial localized away-map action"]
theorem awayCBaseModule_smul_eq_awayMap (f : A) (r : Localization.Away f)
    (x : LocalizedModule.Away (MvPolynomial.C (σ := σ) f) N) :
    letI : Module (Localization.Away f)
        (LocalizedModule.Away (MvPolynomial.C (σ := σ) f) N) :=
      awayCBaseModule (σ := σ) (N := N) f
    r • x =
      (Localization.awayMap (MvPolynomial.C (σ := σ) : A →+* MvPolynomial σ A) f r) • x := sorry

/-- The direct coefficient-away action and the direct localization ring action
form the scalar tower `A_f → A[σ]_(C f) → M_(C f)`. -/
@[stacks 051T "coefficient polynomial localized base module scalar tower"]
theorem awayCBaseModule_isScalarTower (f : A) :
    letI : Algebra (Localization.Away f)
        (Localization.Away (MvPolynomial.C (σ := σ) f)) :=
      awayCAlgebra (σ := σ) f
    letI : Module (Localization.Away f)
        (LocalizedModule.Away (MvPolynomial.C (σ := σ) f) N) :=
      awayCBaseModule (σ := σ) (N := N) f
    IsScalarTower (Localization.Away f)
      (Localization.Away (MvPolynomial.C (σ := σ) f))
      (LocalizedModule.Away (MvPolynomial.C (σ := σ) f) N) := sorry

/-- The named normalized polynomial and coefficient-localization actions form
the scalar tower `Localization.Away f → MvPolynomial σ (Localization.Away f)`. -/
@[stacks 051T "coefficient polynomial localized module scalar tower"]
theorem awayCModule_isScalarTower (f : A) :
    letI : Module (MvPolynomial σ (Localization.Away f))
        (LocalizedModule.Away (MvPolynomial.C (σ := σ) f) N) :=
      awayCModule (σ := σ) (N := N) f
    letI : Module (Localization.Away f)
        (LocalizedModule.Away (MvPolynomial.C (σ := σ) f) N) :=
      awayCBaseModule (σ := σ) (N := N) f
    IsScalarTower (Localization.Away f) (MvPolynomial σ (Localization.Away f))
      (LocalizedModule.Away (MvPolynomial.C (σ := σ) f) N) := sorry

/-- The normalized polynomial action on a coefficient-away localized module
extends its original `MvPolynomial σ A`-module action. -/
@[stacks 051T "coefficient polynomial localized source scalar tower"]
theorem awayCModule_isScalarTower_of_source (f : A) :
    letI : Module (MvPolynomial σ (Localization.Away f))
        (LocalizedModule.Away (MvPolynomial.C (σ := σ) f) N) :=
      awayCModule (σ := σ) (N := N) f
    IsScalarTower (MvPolynomial σ A) (MvPolynomial σ (Localization.Away f))
      (LocalizedModule.Away (MvPolynomial.C (σ := σ) f) N) := sorry

end MvPolynomial.Localization

/-! The coefficient-away module actions are canonical for this normalized
presentation, but the same localized-module carrier also has other useful
scalar descriptions.  Enable this scope only when the normalized chart is the
intended presentation. -/
scoped[MvPolynomial.Localization] attribute [instance 100]
  MvPolynomial.Localization.awayCModule
  MvPolynomial.Localization.awayCBaseModule
  MvPolynomial.Localization.awayCBaseModule_isScalarTower
  MvPolynomial.Localization.awayCModule_isScalarTower
  MvPolynomial.Localization.awayCModule_isScalarTower_of_source

section

open scoped MvPolynomial.Localization

variable {σ : Type u} {A : Type v} [CommRing A]
variable {N : Type w} [AddCommMonoid N] [Module (MvPolynomial σ A) N]
variable (f : A)

attribute [local instance] MvPolynomial.algebraMvPolynomial

#synth Module (MvPolynomial σ (Localization.Away f))
  (LocalizedModule.Away (MvPolynomial.C (σ := σ) f) N)
#synth Module (Localization.Away f)
  (LocalizedModule.Away (MvPolynomial.C (σ := σ) f) N)
#synth IsScalarTower (Localization.Away f)
  (Localization.Away (MvPolynomial.C (σ := σ) f))
  (LocalizedModule.Away (MvPolynomial.C (σ := σ) f) N)
#synth IsScalarTower (Localization.Away f) (MvPolynomial σ (Localization.Away f))
  (LocalizedModule.Away (MvPolynomial.C (σ := σ) f) N)
#synth IsScalarTower (MvPolynomial σ A) (MvPolynomial σ (Localization.Away f))
  (LocalizedModule.Away (MvPolynomial.C (σ := σ) f) N)

end
