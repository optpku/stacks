/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Sequence.Koszul.Homotopy.Family
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.28.6

@stack 0663
-/

/-!
# Lemma 15.28.6

The reusable owners are `KoszulComplex.Family.scalarHomotopyZero` and
`KoszulComplex.Family.span_le_annihilator`; this chapter file is only the source-facing recall.
-/

/- Lemma 15.28.6 (Tag 0663): multiplication by each member of a finite family is null-homotopic
on the associated Koszul complex, and the generated ideal annihilates every homology module. -/
@[stacks 0663 "finite-family Koszul generator null-homotopy"]
#check @KoszulComplex.Family.scalarHomotopyZero

@[stacks 0663 "finite-family Koszul homology annihilator"]
#check @KoszulComplex.Family.span_le_annihilator

#check @HomologicalComplex.Homology.map_smulId_eq_zero_of_nullHomotopy
#check @HomologicalComplex.Homology.mem_annihilator_of_nullHomotopy
#check @HomologicalComplex.Homology.span_le_annihilator_of_nullHomotopy
