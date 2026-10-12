/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.Cyclotomic.Prime
import StacksCheckRecall

@[expose] public section

/- Lemma 9.24.2 (Tag 0EXN): adjoining a primitive `p`th root of unity for a prime `p` gives a
Galois extension whose degree divides `p - 1`. The generic owner first bounds the degree by the
cardinality of `(ZMod n)ˣ` for any nonzero `n`. -/
@[stacks 0EXN]
#check FieldExtension.adjoinPrimitiveRootIsGaloisAndFinrankDvdCardUnits
#check FieldExtension.adjoinPrimitiveRootIsGaloisAndFinrankDvdPrimeSubOne
