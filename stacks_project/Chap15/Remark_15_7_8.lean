/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Pullback.BaseChange.FlatQuotient
import StacksCheckRecall

@[expose] public section

/-!
# Remark 15.7.8

For a finitely presented map `B' ⟶ D'`, relatively flat finitely presented quotients of a
`D'`-module correspond to compatible componentwise quotients after base change.  ReasLib exposes
the displayed base-change and fibre-product functors directly and states that they are categorical
equivalences, without imposing strict equality on chosen quotient objects.

@stack 08KR
-/

@[stacks 08KR "Remark 15.7.8 (1)"]
#check @FiberProductBaseChangeSituation.relativeFpFlatModuleProperty
#check @FiberProductBaseChangeSituation.relativeFpFlatQuotientProperty

@[stacks 08KR "Remark 15.7.8 (2)"]
#check @FiberProductBaseChangeSituation.relativeFpFlatPullbackProperty
#check @FiberProductBaseChangeSituation.relativeFpFlatPullbackQuotientProperty

#check @FiberProductBaseChangeSituation.RelativeFpFlatQuotient.baseChangeFunctor
#check @FiberProductBaseChangeSituation.RelativeFpFlatQuotient.fiberProductFunctor
#check @FiberProductBaseChangeSituation.RelativeFpFlatQuotient.baseChangeFunctor_obj_hom
#check @FiberProductBaseChangeSituation.RelativeFpFlatQuotient.fiberProductUnderFunctor_obj_hom

@[stacks 08KR "Remark 15.7.8"]
#check @FiberProductBaseChangeSituation.RelativeFpFlatQuotient.baseChange_isEquivalence
