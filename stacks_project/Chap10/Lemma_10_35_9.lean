/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.LocalRing.ResidueField.LiesOver
import StacksCheckRecall

/-!
# Lemma 10.35.9

@stack 00GA
-/

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

-- Lemma 10.35.9: if `q` is a prime ideal of `S` lying over a maximal ideal `m` of `R` and the
-- residue field extension `κ(q) / κ(m)` is algebraic, then `q` is maximal.
@[stacks 00GA]
#check @Ideal.ResidueField.LiesOver.isMaximal_of_isAlgebraic

end
