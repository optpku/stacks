/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction.Diagonal

/-!
# Compatibility import for contraction diagonal fibres

This path is retained as requested by the refactor ledger. The contraction
construction corresponds to Stacks Tag 0GHD (Remark 98.27.7 in this snapshot),
not to the elementary distinguished squares of Section 81.9. No claim about
Lemma 81.9.3 or new Stacks tag is attached to this compatibility import.
-/

#check AlgebraicGeometry.AlgebraicSpace.ContractionSituation.represents_diagonalFiber
