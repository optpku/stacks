/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Etale.UnitLift

@[expose] public section

/-!
# Lemma 15.9.1 (07LX)

@stack 07LX
-/

-- Lemma 15.9.1: a quotient unit lifts to a unit after an etale base change preserving the
-- quotient.
@[stacks 07LX "Lemma 15.9.1"]
#check @Algebra.exists_etale_unit_lift_of_quotient

-- Canonical away-localization companion used to construct the source lift.
#check @Algebra.exists_quotientAlgEquiv_localizationAway_of_isUnit_quotient
