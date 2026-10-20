/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.ArtinSchreier
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.116.11

The Artin--Schreier generator and its ramification alternatives are owned by
`DVR.ArtinSchreier`.  This chapter entry is a traceable recall surface; downstream files can import
the ReasLib owner without importing Chapter 10 or the former proof-local normalization helpers.

@stack 09F0
-/

open DVR.ArtinSchreier

/- Lemma 15.116.11, Galois conclusion: the generated Artin--Schreier extension is Galois. -/
@[stacks 09F0 "Lemma 15.116.11, Galois conclusion"]
#check @DVR.ArtinSchreier.isGalois

/- Lemma 15.116.11, cases (1)-(4): the extension lies in one of the four ramification
alternatives. -/
@[stacks 09F0 "Lemma 15.116.11, cases (1)-(4), ramification alternatives"]
#check @DVR.ArtinSchreier.ramificationAlternatives

/- Lemma 15.116.11 (A): parameters in the base DVR force the trivial/unramified alternative. -/
@[stacks 09F0 "Lemma 15.116.11 (A), integral parameter"]
#check @DVR.ArtinSchreier.of_mem

/- Lemma 15.116.11 (B): a denominator prime to `p` forces total ramification. -/
@[stacks 09F0 "Lemma 15.116.11 (B), prime-to-p denominator"]
#check @DVR.ArtinSchreier.totallyRamified

/- In case (3), the totally ramified degree-`p` branch has ramification index exactly `p`. -/
@[stacks 09F0 "case (3), totally ramified branch index"]
#check @DVR.Field.IsTotallyRamified.ramificationIdx_eq_finrank

/- Lemma 15.116.11 (C): a divisible denominator gives the purely inseparable residue
alternative. -/
@[stacks 09F0 "Lemma 15.116.11 (C), divisible-p residue case"]
#check @DVR.ArtinSchreier.residueCase

#check @DVR.ArtinSchreier.Generator
#check @DVR.ArtinSchreier.Generator.spec
#check @DVR.ArtinSchreier.ResidueCase
#check @DVR.ArtinSchreier.ResidueCase.spec
#check @DVR.ArtinSchreier.classify

end
