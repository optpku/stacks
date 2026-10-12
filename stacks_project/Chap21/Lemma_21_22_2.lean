/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Cohomology.IdealPower.MittagLeffler
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.22.2

The two-parameter source family is owned by `PNatInverseSystem.IdealPower.Family`.  Its fixed
towers and rows are canonical, and `SiteModuleCohomology.IdealPower.Eventual` owns the stable
cohomology pieces, their direct sum, grading, and associated-graded action.  This keeps the
eventual-range construction independent of the chapter file and makes the statement reusable for
any site with the required sheaf-cohomology instances.
-/

/- Lemma 21.22.2 (0GYR): Noetherianity of the graded direct sum of stable ideal-power cohomology
pieces implies the Mittag-Leffler condition for the ambient cohomology tower. -/
@[stacks 0GYR]
#check @CategoryTheory.SiteModuleCohomology.IdealPower.Eventual.isMittagLeffler_of_isNoetherian

/- The compatible two-parameter ideal-power family and its diagonal presentation. -/
#check @CategoryTheory.PNatInverseSystem.IdealPower.Family
#check @CategoryTheory.PNatInverseSystem.IdealPower.Family.fixedTower
#check @CategoryTheory.PNatInverseSystem.IdealPower.Family.fixedι
#check @CategoryTheory.PNatInverseSystem.IdealPower.Family.row
#check @CategoryTheory.PNatInverseSystem.IdealPower.Family.row_shortExact
#check @CategoryTheory.PNatInverseSystem.IdealPower.Family.diagonalPresentation
#check @CategoryTheory.PNatInverseSystem.IdealPower.Family.Multiplication

/- The stable-image cohomology owner and its canonical graded action. -/
#check @CategoryTheory.SiteModuleCohomology.IdealPower.Eventual.cohomologyTower
#check @CategoryTheory.SiteModuleCohomology.IdealPower.Eventual.piece
#check @CategoryTheory.SiteModuleCohomology.IdealPower.Eventual.mem_piece_iff
#check @CategoryTheory.SiteModuleCohomology.IdealPower.Eventual.directSum
#check @CategoryTheory.SiteModuleCohomology.IdealPower.Eventual.grade
#check @CategoryTheory.SiteModuleCohomology.IdealPower.Eventual.Action
#check @CategoryTheory.SiteModuleCohomology.IdealPower.Eventual.Action.smul_of
