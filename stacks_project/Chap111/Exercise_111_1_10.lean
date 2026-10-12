/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.LocallyNilpotent.Idempotent
import StacksCheckRecall

@[expose] public section

universe u

/- Exercise 111.1.10: if `I` is a locally nilpotent ideal of a ring `A`, the quotient map
`A → A ⧸ I` induces a bijection on idempotents. -/
@[stacks 078H]
#check (Ideal.IsLocallyNilpotent.quotient_idempotentMap_bijective :
  ∀ {R : Type u} [CommRing R] {I : Ideal R}, I.IsLocallyNilpotent →
    Function.Bijective (Ideal.Quotient.mk I).idempotentMap)
