/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Sheaves.Abelian
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Grothendieck
public import ReasLib.Topology.Sheaves.Abelian.Sheafification

@[expose] public section

namespace CategoryTheory.Sheaf

/-- There exists an abelian sheaf on the real line with its usual topology whose first global
sheaf cohomology group is nonzero. -/
theorem existsRealNonzeroFirstCohomology :
    ∃ F : (TopCat.of ℝ).Sheaf AddCommGrpCat.{0},
      ¬ CategoryTheory.Limits.IsZero
        (F.H' 1 (⊤ : TopologicalSpace.Opens (TopCat.of ℝ))) := sorry

end CategoryTheory.Sheaf
