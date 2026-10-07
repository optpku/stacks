module

public import ReasLib.CategoryTheory.Sites.Cech.Cofinal.FixedTarget
import StacksCheckRecall

@[expose] public section

/- Lemma 21.10.9 (03F9): Cech acyclicity on a cofinal fixed-target covering system implies
positive-degree sheaf-cohomology vanishing, without global finite products in every slice. -/

#check @CategoryTheory.Sheaf.Cech.FixedTarget.Cover
#check @CategoryTheory.Sheaf.Cech.FixedTarget.CofinalSystem
#check @CategoryTheory.Sheaf.Cech.FixedTarget.CofinalSystem.coversTop
#check @CategoryTheory.Sheaf.Cech.FixedTarget.CofinalSystem.target_mem
#check @CategoryTheory.Sheaf.Cech.FixedTarget.CofinalSystem.intersections_mem
#check @CategoryTheory.Sheaf.Cech.FixedTarget.CofinalSystem.exists_refinement
#check @CategoryTheory.Sheaf.Cech.FixedTarget.IsAcyclic

@[stacks 03F9 "fixed-target cofinal Cech cohomology vanishing"]
#check @CategoryTheory.Sheaf.Cech.FixedTarget.IsAcyclic.isZero_cohomology
