/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Sheaf.Cohomology.Cech.ColimitComparison
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Global Cech cohomology on compact Hausdorff spaces

For a compact Hausdorff space, global Cech cohomology agrees with sheaf cohomology in every
degree.  Concrete comparison maps and the reusable filtered-colimit criterion are owned by
`Cech.ColimitComparison`; this leaf records the compact-Hausdorff theorem itself.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe w v u

namespace TopCat.Sheaf.Cohomology.Cech.CompactHausdorff

variable (X : TopCat.{u})
variable [CompactSpace X] [T2Space X]
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v w}]
variable [HasExt.{max u v w} (X.Sheaf AddCommGrpCat.{max u v w})]

/-- On a compact Hausdorff space, global Čech cohomology is isomorphic to sheaf cohomology in every
degree. -/
@[stacks 09V2 "compact-Hausdorff global Cech cohomology comparison"]
theorem isIsomorphic (F : X.Sheaf AddCommGrpCat.{max u v w}) (p : ℕ) :
    IsIsomorphic (cohomology.{w, v, u} F p)
      ((liftedTargetCohomology.{w, v, u} X p).obj F) := sorry

end TopCat.Sheaf.Cohomology.Cech.CompactHausdorff
