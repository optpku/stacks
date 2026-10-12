/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

/-!
# Finite presentation of ideal quotients

This leaf owns the module-theoretic finite-presentation criterion for a quotient
of a commutative ring by an ideal.  It is independent of any particular
projectivity or flatness application.
-/

@[expose] public section

universe u

namespace Module.FinitePresentation

variable {R : Type u} [CommRing R]

/-- The quotient `R ⧸ I` is finitely presented as an `R`-module exactly when the ideal `I` is
finitely generated. -/
theorem quotient_iff_ideal_fg (I : Ideal R) :
    Module.FinitePresentation R (R ⧸ I) ↔ I.FG := sorry

end Module.FinitePresentation
