/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Etale.Dedekind

@[expose] public section

/-!
@stack 0AP2

Lemma 15.44.4 is owned by the reusable etale-over-Dedekind API.  The local conclusion is recalled
through the field-or-DVR alternative because Mathlib's `IsDedekindDomain` includes fields whereas
`IsDiscreteValuationRing` does not.
-/

@[stacks 0AP2 "Lemma 15.44.4 (1)"]
#check @Algebra.Etale.exists_finiteProductOfDedekindDomains
#check @Algebra.Etale.localizationAtMaximal_isField_of_under_eq_bot
#check @Algebra.Etale.localizationAtMaximal_isDVR_of_under_ne_bot
@[stacks 0AP2 "Lemma 15.44.4 (2)"]
#check @Algebra.Etale.localizationAtMaximal_isField_orDVR
