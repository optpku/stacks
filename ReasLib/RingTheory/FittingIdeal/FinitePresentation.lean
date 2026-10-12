/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import ReasLib.RingTheory.FittingIdeal.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Fitting ideals of finitely presented modules

Finite presentations make every intrinsic Fitting ideal finitely generated.
This property is separated from the definition of intrinsic Fitting ideals so
consumers that only need finite modules do not acquire a presentation
hypothesis.
-/

@[expose] public section

universe u v

namespace Module.FinitePresentation

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Every Fitting ideal of a finitely presented module is finitely generated. -/
@[stacks 07ZA "finite generation of Fitting ideals"]
theorem fittingIdeal_fg [Module.FinitePresentation R M] (k : ℕ) :
    (fittingIdeal R M k).FG := sorry

end Module.FinitePresentation
