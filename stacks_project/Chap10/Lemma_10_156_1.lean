/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Henselian.Henselization.BaseChange.AtPrime.QuasiFinite
import StacksCheckRecall

@[expose] public section

/-!
# Quasi-finite base change of henselizations

@stack 05WP

Lemma 10.156.1 is recalled through the explicit-comparison base-change API.
The source's specified comparison is covered by an API stated for every
explicit local comparison, which is the reusable formal generalization rather
than a canonical witness selected from a universal property.
-/

/- Lemma 10.156.1, tag `05WP`: at a finite-type quasi-finite point, the
localized tensor target at the comparison-induced tensor prime is a
henselization; the source comparison is finite, and the library API states
the corresponding conclusion for every explicit local comparison between the
henselizations of `Localization.AtPrime p` and `Localization.AtPrime q`. -/
@[stacks 05WP "localized henselization identification"]
#check @IsHenselizationOf.BaseChange.AtPrime.Tensor.isHenselizationOf
@[stacks 05WP]
#check @IsHenselizationOf.BaseChange.AtPrime.QuasiFiniteAt.comparison_finite
