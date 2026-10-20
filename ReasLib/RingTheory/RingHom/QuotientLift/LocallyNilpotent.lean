/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Smooth.Basic
public import ReasLib.RingTheory.Ideal.LocallyNilpotent
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Smooth lifting across locally nilpotent ideals

This leaf owns the AlgHom-level lifting statement.  The neighboring
`RingHom.QuotientLift.Smooth` leaf owns packaged quotient-lift data; that
`Nonempty` package is intentionally not used as the public interface here,
because the lifting theorem has a prescribed source map as input.
-/

universe u v w

namespace Algebra.Smooth

variable {R : Type u} {S : Type v} {A : Type w}
variable [CommRing R] [CommRing S] [CommRing A]
variable [Algebra R S] [Algebra R A] [Smooth R S]

/-- Lemma 10.138.17: a smooth algebra lifts every map across a locally nilpotent quotient.

The ideal and its local-nilpotence proof stay explicit because they are the concrete extension
being lifted, rather than ambient canonical instances. -/
@[stacks 07K4 "AlgHom lifting across a locally nilpotent ideal"]
theorem exists_lift_of_quotient_by_isLocallyNilpotent
    (I : Ideal A) (hI : I.IsLocallyNilpotent) (f : S →ₐ[R] A ⧸ I) :
    ∃ f' : S →ₐ[R] A, (Ideal.Quotient.mkₐ R I).comp f' = f := sorry

end Algebra.Smooth
