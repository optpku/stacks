/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Ring.Subring.Basic

/-!
# Equalizer subrings

This module characterizes the carrier of the subring on which two ring homomorphisms agree.
-/

@[expose] public section

universe u v

namespace RingHom

variable {R : Type u} {S : Type v} [NonAssocRing R] [Semiring S]

/-- The carrier of the equalizer subring of two ring homomorphisms is their equality locus. -/
@[simp]
theorem coe_eqLocus (f g : R →+* S) :
    (f.eqLocus g : Set R) = {x | f x = g x} := sorry

end RingHom
