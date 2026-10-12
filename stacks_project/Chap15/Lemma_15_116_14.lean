/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.Kummer.Ramification
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.116.14

The Kummer--Artin--Schreier ramification classification is owned by
`KummerArtinSchreier.Ramification`; this file records its Galois conclusion,
four-case classification, and implications `(A)`--`(C)`.

@stack 09F3
-/

namespace Lemma_15_116_14

/- Lemma 15.116.14, Galois conclusion: the presented extension is Galois. -/
@[stacks 09F3 "Lemma 15.116.14, Galois conclusion"]
#check @KummerArtinSchreier.Ramification.isGalois

/- Lemma 15.116.14, cases (1)--(4): the four ramification alternatives. -/
@[stacks 09F3 "Lemma 15.116.14, cases (1)-(4): ramification classification"]
#check @KummerArtinSchreier.Ramification.classification

/- Lemma 15.116.14 (A): an integral right-hand side is trivial or unramified. -/
@[stacks 09F3 "Lemma 15.116.14 (A): integral right-hand side"]
#check @KummerArtinSchreier.Ramification.trivialOrUnramified

/- Lemma 15.116.14 (B): a denominator exponent prime to `p` is totally ramified. -/
@[stacks 09F3 "Lemma 15.116.14 (B): nondivisible denominator exponent"]
#check @KummerArtinSchreier.Ramification.totallyRamified

/- Lemma 15.116.14 (C): a divisible denominator gives the inseparable residue alternative. -/
@[stacks 09F3 "Lemma 15.116.14 (C): divisible denominator exponent"]
#check @KummerArtinSchreier.Ramification.inseparableResidue

#check @KummerArtinSchreier.Ramification.HasInseparableResidue

end Lemma_15_116_14
