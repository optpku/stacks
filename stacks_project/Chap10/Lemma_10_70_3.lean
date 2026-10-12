/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.BaseChange
import StacksCheckRecall

/-!
# Lemma 10.70.3 recall

@stack 0BIP

The extended-center tensor comparison is owned by
`AffineBlowupChart.BaseChange`; the source's conjunction is split into its
atomic reusable consequences there.
-/

@[expose] public section

/- Lemma 10.70.3 (0BIP): the base-change comparison of an affine blowup chart
is surjective, and its kernel is the indicated parameter power torsion. -/
@[stacks 0BIP "base-change comparison"]
#check @AffineBlowupChart.BaseChange.tensorMap

@[stacks 0BIP "base-change comparison surjectivity"]
#check @AffineBlowupChart.BaseChange.tensorMap.surjective

@[stacks 0BIP "base-change comparison kernel membership"]
#check @AffineBlowupChart.BaseChange.tensorMap.mem_ker_iff

@[stacks 0BIP "base-change comparison power torsion kernel"]
#check @AffineBlowupChart.BaseChange.tensorMap.ker_eq_powerTorsion

@[stacks 0BIP "base-change comparison primary kernel"]
#check @AffineBlowupChart.BaseChange.tensorMap.ker_eq_primaryComponent
