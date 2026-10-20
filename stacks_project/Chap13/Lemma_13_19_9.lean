/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.Algebra.Homology.CochainComplex.ProjectiveResolution.Horseshoe
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.19.9 (064C)

The projective horseshoe is the dual of the injective horseshoe and is owned by
`CochainComplex.ProjectiveResolution.Horseshoe`.  Its comparison points from the upper resolving
row to the source short complex, with the right projective resolution prescribed in the data.
The chapter file is intentionally a source-facing recall of the neutral structure and row-level
bridges.
-/

open CategoryTheory

/- Canonical data owner and its row/comparison views. -/
@[stacks 064C "projective horseshoe data"]
#check @CochainComplex.ProjectiveResolution.Horseshoe
@[stacks 064C "projective horseshoe row"]
#check @CochainComplex.ProjectiveResolution.Horseshoe.row
@[stacks 064C "projective horseshoe comparison"]
#check @CochainComplex.ProjectiveResolution.Horseshoe.rowComparison
@[stacks 064C "projective horseshoe middle comparison"]
#check @CochainComplex.ProjectiveResolution.Horseshoe.middleComparison
@[stacks 064C "projective horseshoe middle resolution"]
#check @CochainComplex.ProjectiveResolution.Horseshoe.middleResolution

/- The three comparison components are exposed separately for fine-grained downstream reuse. -/
@[stacks 064C "left comparison"]
#check @CochainComplex.ProjectiveResolution.Horseshoe.leftComparison_quasiIso
@[stacks 064C "right comparison"]
#check @CochainComplex.ProjectiveResolution.Horseshoe.rightComparison_quasiIso
@[stacks 064C "middle comparison"]
#check @CochainComplex.ProjectiveResolution.Horseshoe.middleComparison_quasiIso

/- Prescribed-right and common strict upper-bound refinements. -/
@[stacks 064C "prescribed-right existence"]
#check @CochainComplex.ProjectiveResolution.Horseshoe.nonempty
@[stacks 064C "strict upper bound"]
#check @CochainComplex.ProjectiveResolution.Horseshoe.exists_strictlyLE

/- Source-facing existential bridges. -/
@[stacks 064C "horseshoe existence"]
#check @CochainComplex.ProjectiveResolution.exists_horseshoe
@[stacks 064C "row-level horseshoe existence"]
#check @CochainComplex.ProjectiveResolution.exists_horseshoe_row
@[stacks 064C "strictly nonpositive row-level existence"]
#check @CochainComplex.ProjectiveResolution.exists_horseshoe_row_strictlyLE_zero
