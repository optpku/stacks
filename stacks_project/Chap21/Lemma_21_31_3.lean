/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Category.LCCat.Covering
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.SemiRepresentableFamily.Over

/- Lemma 21.31.3, clause (1): an isomorphism in `LCCat` gives a singleton qc covering. -/
@[stacks 09X1 "(1)"]
#check @IsQuasiCompactCovering.singleton_of_isIso

/- Lemma 21.31.3, clause (2): qc covering families are closed under dependent composition. -/
@[stacks 09X1 "(2)"]
#check @IsQuasiCompactCovering.bind

/- The indexed-arrow presentation of clause (2). -/
@[stacks 09X1 "(2), indexed presentation"]
#check @IsQuasiCompactCovering.ofArrows_bind

/- Lemma 21.31.3, clause (3): qc covering families are stable under base change. -/
@[stacks 09X1 "(3)"]
#check @IsQuasiCompactCovering.baseChange
