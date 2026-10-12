/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Cohomology.Presheaf
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
import StacksCheckRecall

@[expose] public section

/- 20.7.1.1: the restriction map in degree-`n` sheaf cohomology is the map of the canonical
cohomology presheaf induced by an inclusion of opens. -/

open CategoryTheory Opposite TopologicalSpace

universe u

namespace CategoryTheory.Sheaf

variable {X : Type u} [TopologicalSpace X]
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
variable (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ)
variable {U V : Opens X} (hUV : U ≤ V)

@[stacks 01E2 "restriction map in sheaf cohomology"]
#check (((F.cohomologyPresheaf n).map (homOfLE hUV).op) : F.H' n V ⟶ F.H' n U)

end CategoryTheory.Sheaf

end
