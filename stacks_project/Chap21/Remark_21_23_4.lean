/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.Underlying.Cohomology
import StacksCheckRecall

@[expose] public section

/-!
# Remark 21.23.4

The remark is the same canonical Milnor short exact sequence as the preceding lemma, so its
formal entry is a direct recall rather than a second theorem declaration.
-/

/- Remark 21.23.4: objectwise cohomology of a sequential derived limit fits into
`0 ⟶ R¹ lim_n H^(m - 1)(U, K_n) ⟶ H^m(U, K) ⟶ lim_n H^m(U, K_n) ⟶ 0`. -/
@[stacks 0BKW]
#check @RingedSite.Hom.ModuleSections.Underlying.cohomologyShortExact

#check @CategoryTheory.IsDerivedLimit.cohomologyShortExact
