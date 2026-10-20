/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Etale.Neighborhood.ZeroLocus

@[expose] public section

/-!
# Lemma 15.9.4 (07M0)

@stack 07M0
-/

-- Lemma 15.9.4: pointwise etale neighborhoods of `V(J)` yield one etale away-localization
-- defined by an element invertible modulo `J`.
@[stacks 07M0 "Lemma 15.9.4"]
#check @Algebra.exists_quotient_unit_and_etale_away_of_zeroLocus

-- Canonical finite-presentation bridge through `Algebra.etaleLocus`.
#check @Algebra.exists_quotient_unit_and_etale_away_of_zeroLocus_subset_etaleLocus
