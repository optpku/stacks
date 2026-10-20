/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Etale.PolynomialFactorization

@[expose] public section

/-!
# Lemma 15.9.6 (07M1)

@stack 07M1
-/

-- Lemma 15.9.6: the lifting theorem remains valid when the first reduced factor has merely
-- invertible leading coefficient.
@[stacks 07M1 "Lemma 15.9.6"]
#check @Algebra.exists_etale_factorization_lift_of_isUnit_leadingCoeff
