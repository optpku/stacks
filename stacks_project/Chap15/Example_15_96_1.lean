/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Int.Counterexample
import StacksCheckRecall

/-!
# Example 15.96.1

The Berthelot--Ogus endofunctor acts on the regular domain of integer-indexed
cochain complexes.  The shared counterexample owner records the displayed
post-eta triangle explicitly: its first vertex is the degree-`1` single
complex on `(f)`, its cone is `A ⟶ (f)`, and its first map is multiplication
by `f` on `(f)`.  The `shiftIso` datum is the shift identification used by the
last map.  For a nonunit nonzerodivisor, this triangle is not distinguished.

@stack 0GSN
-/

@[stacks 0GSN "Berthelot-Ogus eta endofunctor on the regular domain"]
#check @CochainComplex.BerthelotOgus.Int.domainFunctor

@[stacks 0GSN "category of f-torsion-free modules"]
#check @CochainComplex.BerthelotOgus.Int.Counterexample.moduleProperty

@[stacks 0GSN "homotopy category of f-torsion-free modules"]
#check @CochainComplex.BerthelotOgus.Int.Counterexample.KCategory

@[stacks 0GSN "multiplication into the principal ideal"]
#check @CochainComplex.BerthelotOgus.Int.Counterexample.idealMul

@[stacks 0GSN "multiplication on the principal ideal"]
#check @CochainComplex.BerthelotOgus.Int.Counterexample.idealSelfMul

@[stacks 0GSN "multiplication identifies A with its principal ideal"]
#check @CochainComplex.BerthelotOgus.Int.Counterexample.idealMulIso

@[stacks 0GSN "first complex in the eta counterexample"]
#check @CochainComplex.BerthelotOgus.Int.Counterexample.idealComplex

@[stacks 0GSN "cone complex in the eta counterexample"]
#check @CochainComplex.BerthelotOgus.Int.Counterexample.coneComplex

@[stacks 0GSN "shift identification in the eta counterexample triangle"]
#check @CochainComplex.BerthelotOgus.Int.Counterexample.shiftIso

@[stacks 0GSN "explicit eta-image triangle"]
#check @CochainComplex.BerthelotOgus.Int.Counterexample.triangle

@[stacks 0GSN "ambient image of the eta counterexample triangle"]
#check @CochainComplex.BerthelotOgus.Int.Counterexample.imageTriangle

@[stacks 0GSN "distinguished eta image forces the parameter to be a unit"]
#check @CochainComplex.BerthelotOgus.Int.Counterexample.distinguished_implies_isUnit

@[stacks 0GSN "eta does not preserve the displayed distinguished triangle"]
#check @CochainComplex.BerthelotOgus.Int.Counterexample.not_distinguished

@[stacks 0GSN "ambient eta-image triangle is not distinguished"]
#check @CochainComplex.BerthelotOgus.Int.Counterexample.image_not_distinguished
