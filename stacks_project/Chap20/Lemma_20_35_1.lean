/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Cohomology.IdealPower.MittagLeffler
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 20.35.1

The topological-space statement is a specialization of the site-level one-parameter
ideal-power presentation theorem.  The positive indexing in `Presentation` is only a canonical
shift: `toSequential` is the tower of the sheaves `F (n + 1)`.  Consequently the chapter file
does not redeclare the graded cohomology direct sum or a chapter-specific connecting-image
package.
-/

/- Lemma 20.35.1 (0GYK): Noetherianity of the graded ideal-power cohomology direct sum implies
the Mittag-Leffler condition for the cohomology tower. -/
@[stacks 0GYK]
#check @CategoryTheory.SiteModuleCohomology.IdealPower.isMittagLeffler_of_isNoetherian

#check @CategoryTheory.PNatInverseSystem.IdealPower.Presentation
#check @CategoryTheory.PNatInverseSystem.IdealPower.terms
#check @CategoryTheory.PNatInverseSystem.IdealPower.termInclusion
#check @CategoryTheory.PNatInverseSystem.IdealPower.Presentation.shortExact
#check @CategoryTheory.PNatInverseSystem.IdealPower.Presentation.isSMulSubobject
#check @CategoryTheory.PNatInverseSystem.IdealPower.Multiplication
#check @CategoryTheory.SiteModuleCohomology.piece
#check @CategoryTheory.SiteModuleCohomology.directSum
#check @CategoryTheory.SiteModuleCohomology.grade
#check @CategoryTheory.SiteModuleCohomology.IdealPower.Action
