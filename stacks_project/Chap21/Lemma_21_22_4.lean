/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Cohomology.IdealPower.EventualRange.Topology
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.22.4

The stable-image topology statement is owned by the eventual-range ideal-power cohomology leaf.
The chapter file keeps only the source label and a compact API recall, so the shared theorem has
no dependency on any Chapter 21 file.
-/

/- Lemma 21.22.4 (0GYT): Noetherianity of the stable ideal-power cohomology direct sum identifies
the inverse-limit topology with the adic topology. -/
@[stacks 0GYT]
#check @CategoryTheory.SiteModuleCohomology.IdealPower.Eventual.Site.limitTopology_eq_adic_of_isNoetherian

#check @CategoryTheory.PNatInverseSystem.IdealPower.Family
#check @CategoryTheory.PNatInverseSystem.IdealPower.Family.fixedTower
#check @CategoryTheory.PNatInverseSystem.IdealPower.Family.diagonalPresentation
#check @CategoryTheory.PNatInverseSystem.IdealPower.Family.Multiplication
#check @CategoryTheory.SiteModuleCohomology.IdealPower.Eventual.piece
#check @CategoryTheory.SiteModuleCohomology.IdealPower.Eventual.mem_piece_iff
#check @CategoryTheory.SiteModuleCohomology.IdealPower.Eventual.directSum
#check @CategoryTheory.SiteModuleCohomology.IdealPower.Eventual.Action
