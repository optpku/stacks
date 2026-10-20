module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.RingTheory.Localization.Away.Basic
public import ReasLib.RingTheory.RingHom.QuotientLift.StandardSmooth

@[expose] public section

/-!
# Standard-smooth quotient-lift covers

Smooth algebras admit standard-open covers whose charts have standard-smooth
lifts. Both quotient-map and arbitrary-surjection interfaces are provided.

@stack 04B1
-/

universe u v w

namespace Algebra.Smooth.QuotientLift

variable {R : Type u} {Sbar : Type v} [CommRing R] {I : Ideal R}
variable [CommRing Sbar] [Algebra (R ⧸ I) Sbar]

/-- Lemma 10.137.19, tag `04B1`: a smooth algebra over `R ⧸ I` has a
standard-open cover whose charts lift to standard-smooth quotient lifts. -/
@[stacks 04B1 "standard-smooth lift cover of a smooth quotient algebra"]
theorem exists_standardCover_of_quotient [hSbar : Algebra.Smooth (R ⧸ I) Sbar] :
    ∃ s : Set Sbar, Ideal.span s = ⊤ ∧
      ∀ g ∈ s,
        Nonempty (RingHom.QuotientLift.StandardSmooth.{u, u, v, max u v}
          (Ideal.Quotient.mk I) (Localization.Away g)) := sorry

/-- A smooth algebra over the target of a surjection has a standard-open
cover whose charts lift to standard-smooth algebras over the source. -/
@[stacks 04B1 "standard-smooth lift cover along a surjection"]
theorem exists_standardCover_of_surjective
    {R₀ : Type v} {A₀ : Type w}
    [CommRing R₀] [CommRing A₀] [Algebra R₀ A₀]
    (q : R →+* R₀) (hq : Function.Surjective q) [Algebra.Smooth R₀ A₀] :
    ∃ s : Set A₀, Ideal.span s = ⊤ ∧
      ∀ g ∈ s,
        Nonempty (RingHom.QuotientLift.StandardSmooth.{u, v, w, max u v w}
          q (Localization.Away g)) := sorry

end Algebra.Smooth.QuotientLift
