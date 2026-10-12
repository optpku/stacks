/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Smooth.DVRFactorization
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Ramification

@[expose] public section

/- Situation 16.4.1 is represented by two orthogonal library notions:
`Algebra.DVR.Factorization` owns the flat finite-type factorization `R → A → L`, while
`IsExtensionOfDiscreteValuationRings.WeaklyUnramified` states the ramification-one
condition on the composite DVR map `R → L`. -/
@[stacks 0BJ2]
#check @Algebra.DVR.Factorization
#check @IsExtensionOfDiscreteValuationRings
#check @IsExtensionOfDiscreteValuationRings.WeaklyUnramified
#check @AlgHom.Factorisation.FlatFiniteType
#check @AlgHom.Factorisation.FlatFiniteType.ofId
#check @Algebra.DVR.Factorization.of
#check @Algebra.DVR.Factorization.spec

#check @Algebra.DVR.Factorization.genericIdeal
#check @Algebra.DVR.Factorization.closedIdeal
#check @Algebra.DVR.Factorization.genericPoint
#check @Algebra.DVR.Factorization.closedPoint
