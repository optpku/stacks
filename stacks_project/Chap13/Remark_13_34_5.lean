/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.DerivedCategory.Truncation.Lower.Cochain
import ReasLib.CategoryTheory.DerivedCategory.Truncation.Lower.Comparison
import ReasLib.CategoryTheory.DerivedCategory.Truncation.Lower.Tower.Cone
import StacksCheckRecall

@[expose] public section

/-!
# Remark 13.34.5

The canonical lower derived-truncation tower and its compatible
derived-limit comparisons are neutral derived-category infrastructure. This
source entry records their tagged public API without retaining a chapter-local
Milnor-product implementation.
-/

/- Remark 13.34.5 (Stacks 0H72) (1): `n ↦ τ≥(-n) K` is the canonical lower
derived-truncation tower of a derived object. -/
@[stacks 0H72] #check @CategoryTheory.DerivedCategory.Truncation.Lower.tower

/- Remark 13.34.5 (Stacks 0H72) (2): lower derived-truncation towers are
functorial in the derived object. -/
@[stacks 0H72] #check @CategoryTheory.DerivedCategory.Truncation.Lower.towerFunctor

/- Remark 13.34.5 (Stacks 0H72) (3): the canonical maps from `K` to the tower
stages form a cone, natural in `K`. -/
@[stacks 0H72] #check @CategoryTheory.DerivedCategory.Truncation.Lower.cone

/- Remark 13.34.5 (Stacks 0H72) (4): a compatible derived-limit comparison
is represented by the generic `HomotopyLimit.Comparison` data structure and
specialized to the canonical lower-truncation tower. -/
@[stacks 0H72] #check @CategoryTheory.HomotopyLimit.Comparison
@[stacks 0H72] #check @CategoryTheory.DerivedCategory.Truncation.Lower.Comparison

/- Remark 13.34.5 (Stacks 0H72) (5): compatible maps to lower-truncation
derived limits are simultaneously isomorphisms. -/
@[stacks 0H72] #check
  @CategoryTheory.DerivedCategory.Truncation.Lower.Comparison.Exists.isIso_iff

/- Remark 13.34.5 (Stacks 0H72) (6): for every cutoff, the abstract
`t`-structure truncation of `Q.obj K` maps canonically and invertibly to the
derived image of the concrete cochain truncation. -/
@[stacks 0H72] #check @CategoryTheory.DerivedCategory.TruncGE.qHom

/- Remark 13.34.5 (Stacks 0H72) (7): after deleting the initial `τ≥0` stage,
the tower `n ↦ τ≥(-n) (Q.obj K)` has a canonical comparison with the derived
concrete tower `n ↦ Q.obj (K.truncGE (-(n + 1)))`; this comparison is an
isomorphism of sequential inverse systems. -/
@[stacks 0H72] #check
  @CategoryTheory.DerivedCategory.Truncation.Lower.Cochain.towerHom
@[stacks 0H72] #check
  @CategoryTheory.DerivedCategory.Truncation.Lower.Cochain.towerHom_isIso
