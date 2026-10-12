/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Localization.Free
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.MvPolynomial.Localization.Module

/-!
# Free Modules on Coefficient Localization Charts

This leaf records the reusable freeness interface for the normalized chart
`MvPolynomial σ (Localization.Away f)`.  It deliberately leaves the
underlying scalar action in `MvPolynomial.Localization`, where competing
presentations of the same localized module are kept scoped.

@stack 051S
@stack 051T
-/

@[expose] public section

universe u v w

namespace MvPolynomial.Localization

variable {σ : Type u} {A : Type v} [CommRing A]

open scoped MvPolynomial.Localization

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Tag `051T`: the coefficient-away polynomial localization itself is free
over the coefficient localization. -/
@[stacks 051T "coefficient polynomial localization freeness"]
theorem awayCAlgebra_free (f : A) :
    Module.Free (Localization.Away f)
      (Localization.Away (MvPolynomial.C (σ := σ) f)) := sorry

section

variable {N : Type w} [AddCommMonoid N] [Module (MvPolynomial σ A) N]

/-- Tag `051T`: freeness over the polynomial localization away from `C f`
restricts to freeness over the coefficient localization away from `f`. -/
@[stacks 051T "coefficient localization restriction of freeness"]
theorem awayC_free_of_localized_free (f : A)
    [Module.Free (Localization.Away (MvPolynomial.C (σ := σ) f))
      (LocalizedModule.Away (MvPolynomial.C (σ := σ) f) N)] :
    Module.Free (Localization.Away f)
      (LocalizedModule.Away (MvPolynomial.C (σ := σ) f) N) := sorry

/-- Tag `051T`: coefficient-chart freeness persists after enlarging the
principal denominator from `f` to `f * g`. -/
@[stacks 051T "coefficient localization product denominator freeness"]
theorem awayC_free_mul (f g : A)
    [Module.Free (Localization.Away f)
      (LocalizedModule.Away (MvPolynomial.C (σ := σ) f) N)] :
    Module.Free (Localization.Away (f * g))
      (LocalizedModule.Away (MvPolynomial.C (σ := σ) (f * g)) N) := sorry

end

section

variable {N : Type w} [AddCommGroup N] [Module (MvPolynomial σ A) N]

/-- Tag `051S`: a finitely presented module over a multivariate polynomial
ring becomes free after inverting one nonzero coefficient. -/
@[stacks 051S "coefficient generic freeness for finitely presented polynomial modules"]
theorem exists_nonzero_awayC_free [IsDomain A]
    [Module.FinitePresentation (MvPolynomial σ A) N] :
    ∃ f : A, f ≠ 0 ∧
      Module.Free (Localization.Away f)
        (LocalizedModule.Away (MvPolynomial.C (σ := σ) f) N) := sorry

end

end MvPolynomial.Localization
