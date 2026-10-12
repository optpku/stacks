/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.FieldTheory.PBasis.MixedPowerSeries.Properties

@[expose] public section

/-!
# Lemma 15.46.5

Lemma 15.46.5 is owned by the mixed p-power subring API.  Its three source clauses are recalled
separately below.

@stack 07P5
-/

/- @stack 07P5 -- Lemma 15.46.5 (1): intersection. -/
@[stacks 07P5 "Lemma 15.46.5 (1)"]
#check @FieldExtension.PBasis.pthPowerMixedSubring.fractionSubfield_iInf_eq_frobenius

/- @stack 07P5 -- Lemma 15.46.5 (2): directedness. -/
@[stacks 07P5 "Lemma 15.46.5 (2)"]
#check @FieldExtension.PBasis.pthPowerMixedSubring.fractionSubfield_directed

/- @stack 07P5 -- Lemma 15.46.5 (3): finiteness. -/
@[stacks 07P5 "Lemma 15.46.5 (3)"]
#check @FieldExtension.PBasis.pthPowerMixedSubring.moduleFinite

end
