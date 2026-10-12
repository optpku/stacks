/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.Formal.Single
import StacksCheckRecall

@[expose] public section

/-!
# Theorem 15.90.18 (05ES)

@stack 05ES
-/

-- Theorem 15.90.18, the canonical single-principal-open formal-gluing functor.
@[stacks 05ES "Theorem 15.90.18, formal-gluing functor"]
#check @LocalizedModule.Away.FormalGluing.Single.functor

-- Theorem 15.90.18, equivalence under flatness and quotient preservation.
@[stacks 05ES "Theorem 15.90.18, equivalence"]
#check @LocalizedModule.Away.FormalGluing.Single.functor_isEquivalence_of_flat_of_quotientMap_bijective
