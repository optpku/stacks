/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.FinitePresentation
public import ReasLib.Algebra.Module.FinitePresentation.Relative
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Presentation-independent relative finite presentation

These characterizations let downstream code choose the polynomial or finitely
presented cover best suited to the argument without unpacking the owner.
-/

universe u v w x

namespace Module.FinitePresentationRelativeTo

variable {R : Type u} {A : Type v} {M : Type w}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module A M]

/-- Over a finite type algebra, relative finite presentation may be checked
on every surjective finite-variable polynomial presentation. -/
@[stacks 05GY "every polynomial presentation"]
theorem iff_overEveryPolynomialPresentation [Algebra.FiniteType R A] :
    Module.FinitePresentationRelativeTo R A M ↔
      ∀ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A)
        (_ : Function.Surjective α), Module.FinitePresentationAlong α.toRingHom M := sorry
/- Proof strategy: for the forward direction, compare the witness presentation with an arbitrary
surjective finite-variable presentation through a common polynomial refinement and transport
module finite presentation across the two surjections.  Conversely, choose the finite-variable
surjective presentation supplied by `Algebra.FiniteType` and package its specialization in the
definition of `FinitePresentationRelativeTo`. -/

/-- A relatively finitely presented module is finitely presented over any chosen surjective
finite-variable polynomial presentation of the ambient algebra. -/
@[stacks 05GY "chosen polynomial presentation"]
theorem overPolynomialPresentation (hM : Module.FinitePresentationRelativeTo R A M)
    (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A)
    (hα : Function.Surjective α) :
    Module.FinitePresentationAlong α.toRingHom M := sorry
/- Proof strategy: obtain `Algebra.FiniteType R A` from `hM.finiteType`, then apply the forward
direction of `iff_overEveryPolynomialPresentation` to `hM`, `α`, and `hα`. -/

/-- Over a finite type algebra, relative finite presentation may be checked
after restriction to every surjective finitely presented algebra cover in a universe
at least as large as that of `R`. This includes `ULift` of every finite-variable
polynomial algebra over `R`, so the reverse criterion cannot be vacuous. -/
@[stacks 05GY "every finitely presented cover"]
theorem iff_overAnyFinitelyPresentedCover [Algebra.FiniteType R A] :
    Module.FinitePresentationRelativeTo R A M ↔
      ∀ (A' : Type (max u x)) [CommRing A'] [Algebra R A'] [Algebra.FinitePresentation R A']
        (f : A' →ₐ[R] A) (_ : Function.Surjective f),
          Module.FinitePresentationAlong f.toRingHom M := sorry
/- Proof strategy: refine a finitely presented cover `A' → A` by a finite-variable polynomial
presentation of `A'`, compose the two algebra maps, and use
`iff_overEveryPolynomialPresentation`; for the reverse implication, specialize to a polynomial
algebra cover of `A`, lifted to `Type (max u x)` using `ULift.algEquiv`.
Transport finite presentation back along this genuine algebra equivalence. -/

/-- A relatively finitely presented module is finitely presented after restriction to any
surjective finitely presented algebra cover. -/
@[stacks 05GY "chosen finitely presented cover"]
theorem overAnyFinitelyPresentedCover (hM : Module.FinitePresentationRelativeTo R A M)
    (A' : Type x) [CommRing A'] [Algebra R A'] [Algebra.FinitePresentation R A']
    (f : A' →ₐ[R] A) (hf : Function.Surjective f) :
    Module.FinitePresentationAlong f.toRingHom M := sorry
/- Proof strategy: choose a finite-variable polynomial presentation of `A'`. Its composite
with `f` is surjective, so `overPolynomialPresentation` applies. Descend module finite
presentation across the finitely presented quotient onto `A'`, as in Stacks tag 05GY.
This argument works for every cover universe `x`, independently of the universe used
in the reverse criterion. -/

end Module.FinitePresentationRelativeTo
