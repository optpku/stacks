/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Cohomology.IdealPower.Topology
import StacksCheckRecall

@[expose] public section

/- Lemma 20.35.3 uses the reusable exact-degree ideal-power cohomology API.  The source-facing
owner retains the topological space, the sheaf tower, its short exact ideal-power rows, and the
positive indexing of the cohomology tower. -/

#check @CategoryTheory.PNatInverseSystem
#check @CategoryTheory.PNatInverseSystem.IdealPower.Presentation
#check @CategoryTheory.PNatInverseSystem.IdealPower.terms
#check @CategoryTheory.PNatInverseSystem.IdealPower.termInclusion
#check @CategoryTheory.PNatInverseSystem.degreeTransition
#check @CategoryTheory.PNatInverseSystem.IdealPower.Multiplication
#check @CategoryTheory.PNatInverseSystem.stepRow
#check @CategoryTheory.PNatInverseSystem.IsStepShortExact
#check @CategoryTheory.PNatInverseSystem.IsIdealPowerTerms
#check @CategoryTheory.PNatInverseSystem.IsIdealPowerQuotient
#check @Ideal.IsSMulSubobject
#check @Ideal.smulSubobject
#check @CategoryTheory.SiteModuleCohomology.piece
#check @CategoryTheory.SiteModuleCohomology.directSum
#check @CategoryTheory.SiteModuleCohomology.grade
#check @CategoryTheory.SiteModuleCohomology.IdealPower.IsCanonicalAction
#check @CategoryTheory.SiteModuleCohomology.IdealPower.Action

@[stacks 0GYM]
#check @CategoryTheory.SiteModuleCohomology.IdealPower.limitTopology_eq_adic_of_isNoetherian

/- The site-level companion and its pure algebraic filtration criterion are reusable independently
of the topological-space presentation. -/
#check @CategoryTheory.SiteModuleCohomology.IdealPower.Site.limitTopology_eq_adic_of_isNoetherian
#check @CategoryTheory.SequentialInverseSystem.limitTopology_eq_adic_of_isNoetherian
