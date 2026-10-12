/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.Cotangent.KaehlerFiber
import StacksCheckRecall

/-!
@stack 00TR

Lemma 10.140.1 is the closed-point quotient presentation of the canonical
Kähler-fiber/cotangent finrank comparison.  The reusable owner is
`Ideal.Cotangent.finrank_kaehlerFiber_eq_quotientCotangent`; this chapter file
keeps only the source-labelled recall.
-/

@[expose] public section

@[stacks 00TR "separable residue-field comparison owner"]
#check @Ideal.Cotangent.kaehlerFiberEquiv

@[stacks 00TR "closed-point quotient-cotangent comparison"]
#check @Ideal.Cotangent.finrank_kaehlerFiber_eq_quotientCotangent

@[stacks 00TR "residue-field cotangent comparison"]
#check @Ideal.Cotangent.finrank_residueField_kaehlerFiber_eq_cotangent

@[stacks 00TR "localization-at-prime comparison"]
#check @Ideal.Cotangent.finrank_kaehlerFiber_eq_localizationAtPrime
