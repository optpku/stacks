/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.GrothendieckGroup.Graded.Periodic
import StacksCheckRecall

@[expose] public section

/-!
# Remark 10.58.8

The eventually quasi-polynomial graded-piece theorem is a reusable K0 result, so this chapter entry is a canonical
recall rather than a second theorem owner.

@stack 02CD
-/

/- API design: the recalled theorem uses `Submodule R M` pieces and derives finite type from
Noetherianity inside `gradedPieceClass_of_isNoetherian`; no chapter-local Veronese package or
instance is exposed. -/

/- Remark 10.58.8 (Tag 02CD): the K0-valued homogeneous-piece function of a finite module over a
Noetherian graded algebra is eventually quasi-polynomial (the source calls this periodic
numerical-polynomial behavior). -/
@[stacks 02CD]
#check @CategoryTheory.ModuleCat.K0.gradedPieceClass_eventuallyQuasiPolynomial

/- Remark 10.58.8 support: eventually quasi-polynomial functions are assembled residue class by
residue class in the generic numerical-polynomial owner. -/
#check @EventuallyQuasiPolynomial.ofResidueSlices
