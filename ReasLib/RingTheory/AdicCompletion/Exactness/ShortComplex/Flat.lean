/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.LinearAlgebra.QuotientByIdeal.Exact
public import ReasLib.LinearAlgebra.QuotientByIdeal.Flat
public import ReasLib.LinearAlgebra.QuotientByIdeal.Reduction
public import ReasLib.RingTheory.AdicCompletion.Exactness.ShortComplex

/-!
# Flat-cokernel exactness after adic completion

@stack 0315

This leaf gives the flatness-based short-exactness criterion.  It depends on
ideal-quotient exactness but not on Noetherian or finiteness hypotheses.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AdicCompletion

variable {R : Type u} [CommRing R]

/-- Tag `0315`: completing a short exact sequence remains short exact when its cokernel is flat. -/
@[stacks 0315 "adic completion of a flat-cokernel short exact sequence"]
theorem mapShortComplex_shortExact_of_flat
    (I : Ideal R) {S : ShortComplex (ModuleCat.{u} R)}
    (hS : S.ShortExact) [Module.Flat R S.X₃] :
    (mapShortComplex I S).ShortExact := sorry

end AdicCompletion
