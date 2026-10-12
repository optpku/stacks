/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.LinearAlgebra.QuotientByIdeal.Projective.Flat
import StacksCheckRecall

/-!
# Lemma 10.77.7 recall

The reusable owner is `Module.Projective.of_flat_of_quotient_of_isNilpotent`.  It is stated for a
flat module over a commutative ring and a projective quotient by a nilpotent ideal, without the
chapter's auxiliary quotient-exactness proof graph.

@stack 05CG
-/

@[expose] public section

/- Lemma 10.77.7 (05CG): if `I` is a nilpotent ideal of a commutative ring `R`, `M / IM` is a
projective `R ⧸ I`-module, and `M` is flat over `R`, then `M` is projective over `R`. -/
@[stacks 05CG] #check @Module.Projective.of_flat_of_quotient_of_isNilpotent
