/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.IntegralClosure.Ramification
public import ReasLib.RingTheory.Henselian.IntegralClosure.PrimeFiber
import StacksCheckRecall

@[expose] public section

/-!
# Remark 15.112.6

The integral-closure facts are recalled from their canonical Mathlib and ReasLib owners.

@stack 09E8
-/

/- Remark 15.112.6 (1): the integral closure is finite over the base DVR. -/
@[stacks 09E8 "Remark 15.112.6 (1): finite integral closure"]
#check @integralClosure.moduleFinite_of_fractionField

/- Remark 15.112.6 (2): the integral closure is a Dedekind domain. -/
@[stacks 09E8 "Remark 15.112.6 (2): Dedekind integral closure"]
#check @integralClosure.isDedekindDomain_fractionRing

/- Remark 15.112.6 (3): the degree is the sum of ramification indices times inertia degrees. -/
@[stacks 09E8 "Remark 15.112.6 (3): ramification-inertia formula"]
#check @integralClosure.Ramification.finrank_eq_sum

/- Remark 15.112.6 (4): a henselian base has a unique prime above its maximal ideal. -/
@[stacks 09E8 "Remark 15.112.6 (4): henselian prime fiber"]
#check @integralClosure.Henselian.primesOver_eq_singleton
