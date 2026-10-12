/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Determinant
import StacksCheckRecall

/-!
# Lemma 15.123.4 (0FJM)

The determinant line, its functoriality, the intrinsic rank-zero predicate, and the canonical
element must be chosen coherently.  ReasLib therefore owns them as
`PerfectDerived.TorNegOneZero.Determinant`; this chapter file is the source-facing recall.

@stack 0FJM
-/

@[expose] public section

open CategoryTheory

/- Lemma 15.123.4: a coherent determinant functor and canonical element exist. -/
@[stacks 0FJM "Lemma 15.123.4: determinant functor and canonical element"]
#check @PerfectDerived.TorNegOneZero.nonemptyDeterminant

#check @PerfectDerived.TorNegOneZero
#check @PerfectDerived.TorNegOneZero.Determinant
#check @PerfectDerived.TorNegOneZero.Determinant.det
#check @PerfectDerived.TorNegOneZero.Determinant.line
#check @PerfectDerived.TorNegOneZero.Determinant.rankZero_iff
#check @PerfectDerived.TorNegOneZero.Determinant.map_canonicalElement
#check @PerfectDerived.TorNegOneZero.Determinant.representativeIso_hom_canonicalElement

#print axioms PerfectDerived.TorNegOneZero.Determinant
#print axioms PerfectDerived.TorNegOneZero.Determinant.det
#print axioms PerfectDerived.TorNegOneZero.nonemptyDeterminant

end
