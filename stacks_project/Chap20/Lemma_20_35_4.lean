/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Cohomology.IdealPower.EventualRange.Topology
import StacksCheckRecall

@[expose] public section

/- Lemma 20.35.4 uses the reusable two-parameter family
`(n, m) ↦ I ^ n • F (m + 1)`.  Its term `N n` is the stable image in exact cohomological degree
`p`; no `p + 1` shift occurs in this lemma. -/

#check @CategoryTheory.PNatInverseSystem.IdealPower.Family
#check @CategoryTheory.PNatInverseSystem.IdealPower.Family.fixedTower
#check @CategoryTheory.PNatInverseSystem.IdealPower.Family.fixedι
#check @CategoryTheory.PNatInverseSystem.IdealPower.Family.row
#check @CategoryTheory.PNatInverseSystem.IdealPower.Family.diagonalPresentation
#check @CategoryTheory.PNatInverseSystem.IdealPower.Family.Multiplication
#check @CategoryTheory.Functor.stableImage
#check @CategoryTheory.SiteModuleCohomology.IdealPower.Eventual.cohomologyTower
#check @CategoryTheory.SiteModuleCohomology.IdealPower.Eventual.piece
#check @CategoryTheory.SiteModuleCohomology.IdealPower.Eventual.mem_piece_iff
#check @CategoryTheory.SiteModuleCohomology.IdealPower.Eventual.directSum
#check @CategoryTheory.SiteModuleCohomology.IdealPower.Eventual.grade
#check @CategoryTheory.SiteModuleCohomology.IdealPower.Eventual.IsCanonicalAction
#check @CategoryTheory.SiteModuleCohomology.IdealPower.Eventual.Action

@[stacks 0GYN]
#check @CategoryTheory.SiteModuleCohomology.IdealPower.Eventual.limitTopology_eq_adic_of_isNoetherian

/- The site-level theorem is reusable independently of the topological-space presentation. -/
#check @CategoryTheory.SiteModuleCohomology.IdealPower.Eventual.Site.limitTopology_eq_adic_of_isNoetherian
