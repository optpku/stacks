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

/-- The source-defined compact-Hausdorff Cech-to-cohomology map is an isomorphism in every degree. -/
@[stacks 09V2 "compact-Hausdorff global Cech cohomology comparison"]
theorem isIsomorphic
    {p : ℕ} (c : Comparison.{w, v, u} (X := X) p)
    (F : X.Sheaf AddCommGrpCat.{max u v w}) :
    IsIso ((comparison c.map).app F) :=
  Comparison.isIso_app c F

end TopCat.Sheaf.Cohomology.Cech.CompactHausdorff
