/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.ZeroObject
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory.Limits

/- Lemma 12.3.2 [00ZZ] (1): the source's three-way equivalence is represented by the canonical
zero-object criterion and its initial/terminal consequences, rather than a source-specific `TFAE`
list. -/
@[stacks 00ZZ]
#check @IsZero.iff_id_eq_zero

@[stacks 00ZZ]
#check @IsInitial.isZero

@[stacks 00ZZ]
#check @IsTerminal.isZero

@[stacks 00ZZ]
#check @IsZero.isInitial

@[stacks 00ZZ]
#check @IsZero.isTerminal

/- Lemma 12.3.2 [00ZZ] (2): factorization through a fixed zero object is owned by the reusable
zero-object bridge. -/
@[stacks 00ZZ]
#check @IsZero.factors_through_iff_eq_zero

end CategoryTheory.Limits
