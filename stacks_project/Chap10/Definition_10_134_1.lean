/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.Derived
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.RestrictScalars
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.134.1

@stack 07BN
-/

/- Definition 10.134.1 [stacks 07BN]: canonical recall of the presentation-level
naive cotangent complex.  The reusable owner is
`Algebra.Extension.NaiveCotangent.complex`; the algebra-level and derived views are
separate ReasLib companions rather than Chapter 10 aliases. -/
@[stacks 07BN]
#check @Algebra.Extension.NaiveCotangent.complex

/- Companion views of the same construction. -/
#check @Algebra.Extension.NaiveCotangent.restrictScalars
#check @Algebra.Extension.NaiveCotangent.restrictScalarsAlong
#check @Algebra.Extension.NaiveCotangent.restrictScalars_d_succ_succ
#check @Algebra.Extension.NaiveCotangent.restrictScalarsAlong_d_succ_succ
#check @Algebra.Extension.NaiveCotangent.chainMap
#check @Algebra.Extension.NaiveCotangent.chainMap_id
#check @Algebra.Extension.NaiveCotangent.chainMap_comp
#check @Algebra.Extension.NaiveCotangent.generatorsHomotopyEquiv
#check @Algebra.naiveCotangent
#check @Algebra.naiveCotangentObject
#check @CommRingCat.Hom.naiveCotangent
#check @CommRingCat.Hom.naiveCotangentObject
