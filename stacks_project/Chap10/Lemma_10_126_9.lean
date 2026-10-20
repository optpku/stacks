/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Algebra.Quotient.LocallyNilpotent
import StacksCheckRecall

/-!
# Lemma 10.126.9

@stack 07RD
-/

@[expose] public section

/- Lemma 10.126.9 (Tag 07RD): a finite-type target algebra map is surjective when its raw
base-ideal quotient projection is surjective.  The source-facing shape is owned by
`AlgHom.BaseIdeal.surjective_of_quotient_mk_surjective`; the bundled quotient form remains
available as `surjective_of_quotient_surjective`, so callers can choose the abstraction level
without duplicating quotient data. -/
@[stacks 07RD]
#check @AlgHom.BaseIdeal.surjective_of_quotient_mk_surjective

@[stacks 07RD]
#check @AlgHom.BaseIdeal.surjective_of_quotient_surjective
