/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RegularLocalRing.Quotient
import StacksCheckRecall

@[expose] public section

/-!
# Regular local rings and regular sequence quotients

Lemma 10.106.7 is owned by the principal and regular-sequence quotient
criteria in `ReasLib.RingTheory.RegularLocalRing.Quotient`.

@stack 00NU
-/

/- Lemma 10.106.7 (1): if `x` is a regular element of the maximal ideal and
`R ⧸ Ideal.span {x}` is regular local, then `R` is regular local. -/
@[stacks 00NU "(1)"]
#check @IsRegularLocalRing.of_quotient_span_singleton_of_isRegular

/- Lemma 10.106.7 (2): more generally, regular-locality of a quotient by a
regular sequence lifts to the ambient Noetherian local ring. -/
@[stacks 00NU "(2)"]
#check @IsRegularLocalRing.of_quotient_of_isRegular
