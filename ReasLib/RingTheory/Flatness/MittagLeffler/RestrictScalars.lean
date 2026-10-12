/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.FinitePresentation
public import ReasLib.RingTheory.Flatness.MittagLeffler
import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Restrict
import ReasLib.Algebra.Module.FinitePresentation.RestrictScalars
import ReasLib.RingTheory.Finiteness.Quotient

/-!
# Restriction of scalars for Mittag-Leffler modules

Finite, finitely presented ring maps preserve the Mittag-Leffler property under restriction of
scalars.  This is a theorem rather than an instance: the intermediate ring is not determined by
the target proposition `Module.MittagLeffler R M`.
-/

@[expose] public section

universe u v w

namespace Module.MittagLeffler

namespace RestrictScalars

section RingHom

variable {R : Type u} {S : Type v} [Ring R] [Ring S]

namespace Surjective

/-- Explicit-hypothesis core for restriction along a surjective ring homomorphism: finite
presentation of the restricted regular target module makes Mittag-Lefflerness invariant. -/
@[stacks 05CR "surjective restriction explicit API"]
theorem iff_of_finitePresentation (f : R →+* S) (hf : Function.Surjective f)
    (hfp : Module.FinitePresentation R
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S)))
    (N : ModuleCat.{w} S) :
    MittagLeffler R ((ModuleCat.restrictScalars f).obj N) ↔
      MittagLeffler S N := sorry

end Surjective

/-- Restriction along a surjective ring homomorphism preserves and reflects the
Mittag-Leffler property when the restricted regular target module is finitely presented. -/
@[stacks 05CR "surjective restriction"]
theorem iff_of_surjective (f : R →+* S) [RingHomSurjective f]
    [Module.FinitePresentation R
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S))]
    (N : ModuleCat.{w} S) :
    MittagLeffler R ((ModuleCat.restrictScalars f).obj N) ↔
      MittagLeffler S N := sorry

end RingHom

end RestrictScalars

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

namespace RestrictScalars

/-- A Mittag-Leffler module remains Mittag-Leffler after restriction along a ring extension that
is finitely presented as a module. -/
@[stacks 05CQ "module finite presentation"]
theorem of_finitePresentation [Module.FinitePresentation R S]
    (hM : MittagLeffler S M) : MittagLeffler R M := sorry

/-- Restriction of scalars along an algebra equivalence preserves the Mittag-Leffler property
without requiring callers to install finite-presentation instances for the equivalence. -/
@[stacks 05CQ "algebra equivalence"]
theorem of_equiv (e : S ≃ₐ[R] R) (hM : MittagLeffler S M) :
    MittagLeffler R M := sorry

/-- Restriction of scalars along an algebra equivalence preserves and reflects the
Mittag-Leffler property. -/
@[stacks 05CQ "algebra equivalence iff"]
theorem iff_of_equiv (e : S ≃ₐ[R] R) :
    MittagLeffler R M ↔ MittagLeffler S M := sorry

end RestrictScalars

/-- Lemma 10.88.11, tag `05CQ`: a Mittag-Leffler module remains Mittag-Leffler after restricting
scalars along a finite, finitely presented ring map. -/
@[stacks 05CQ]
theorem restrictScalars [Module.Finite R S] [Algebra.FinitePresentation R S]
    (hM : MittagLeffler S M) : MittagLeffler R M := sorry

namespace RestrictScalars

/-- Lemma 10.88.12, tag `05CR`: for a finitely generated ideal, the Mittag-Leffler property of a
quotient module is independent of whether scalars are taken over the ring or its quotient. -/
@[stacks 05CR]
theorem iff_quotient (I : Ideal R) (hI : I.FG) (N : ModuleCat.{w} (R ⧸ I)) :
    MittagLeffler R
        ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj N) ↔
      MittagLeffler (R ⧸ I) N := sorry

end RestrictScalars

end Module.MittagLeffler
