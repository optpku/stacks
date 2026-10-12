/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.Pure
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Finiteness.Projective.Flat
public import ReasLib.RingTheory.Finiteness.Quotient

/-!
# Projective Quotients by Pure Ideals

This leaf combines the canonical flatness meaning of `Ideal.Pure` with the
finite-presentation criterion for ideal quotients and the finite-projective
criterion. It is independent of any particular source-chapter application.
-/

@[expose] public section

universe u

namespace Ideal.Pure

variable {R : Type u} [CommRing R]

/-- The quotient by an ideal is projective exactly when the ideal is pure and finitely
generated. -/
@[stacks 05KK "projective quotient by a pure finitely generated ideal"]
theorem iff_projective_quotient (I : Ideal R) :
    I.Pure ∧ I.FG ↔ Module.Projective R (R ⧸ I) := sorry

end Ideal.Pure
