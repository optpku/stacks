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
# Lemma 20.35.2

The topological-space presentation is a specialization of the site-level two-parameter
ideal-power API.  The canonical `Family` packages the compatible squares and short exact rows;
the `Eventual` namespace packages the stable ranges and the graded action.  No Chapter 21 import
is needed here.
-/

/- Lemma 20.35.2: the stable ideal-power cohomology criterion implies Mittag-Leffler for the
cohomology tower. -/
@[stacks 0GYL]
#check @CategoryTheory.SiteModuleCohomology.IdealPower.Eventual.isMittagLeffler_of_isNoetherian

#check @CategoryTheory.PNatInverseSystem.IdealPower.Family
#check @CategoryTheory.PNatInverseSystem.IdealPower.Family.row
#check @CategoryTheory.PNatInverseSystem.IdealPower.Family.row_shortExact
#check @CategoryTheory.PNatInverseSystem.IdealPower.Family.diagonalPresentation
#check @CategoryTheory.SiteModuleCohomology.IdealPower.Eventual.cohomologyTower
#check @CategoryTheory.SiteModuleCohomology.IdealPower.Eventual.piece
#check @CategoryTheory.SiteModuleCohomology.IdealPower.Eventual.mem_piece_iff
#check @CategoryTheory.SiteModuleCohomology.IdealPower.Eventual.directSum
#check @CategoryTheory.SiteModuleCohomology.IdealPower.Eventual.Action
