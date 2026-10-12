/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Valuation.ResiduePreimage
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.50.10

@stack 088Z

The source construction is the residue preimage of the valuation subring of
`ResidueField A'` determined by `A`.  The reusable owner is
`ValuationSubring.residuePreimage`; the source hypotheses identify the chosen
subring with the image of `algebraMap A (ResidueField A')` through
`ValuationRing.range_algebraMap_eq`.  The owner API is stronger: it accepts an
arbitrary valuation subring of the residue field and exposes its membership,
maximal ideal, and valuation-ring structures independently of a presentation.
-/

/- Lemma 10.50.10 (1) (Tag 088Z): residue-preimage construction and membership. -/
@[stacks 088Z]
#check @ValuationSubring.residuePreimage
@[stacks 088Z]
#check @ValuationSubring.mem_residuePreimage_iff
@[stacks 088Z]
#check @ValuationSubring.mem_residuePreimage_of_mem_maximalIdeal

/- Lemma 10.50.10 (2) (Tag 088Z): the maximal ideal is the residue-field maximal-ideal comap. -/
@[stacks 088Z]
#check @ValuationSubring.maximalIdeal_residuePreimage
@[stacks 088Z]
#check @ValuationSubring.mem_maximalIdeal_residuePreimage_iff

/- Lemma 10.50.10 (3) (Tag 088Z): valuation-ring inheritance for the preimage. -/
@[stacks 088Z]
#check @ValuationSubring.residuePreimage_isValuationRing

/- Source-specialization bridge: the valuation subring attached to `A` has the
   same underlying subring as the image of `algebraMap A (ResidueField A')`. -/
@[stacks 088Z]
#check @ValuationRing.range_algebraMap_eq
