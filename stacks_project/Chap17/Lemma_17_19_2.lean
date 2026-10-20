/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaf.Presentation
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopCat TopologicalSpace

noncomputable section

universe u

variable {X : TopCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
variable {B : Set (Opens X)} (hB : Opens.IsBasis B)
variable (hcompact : ∀ U, U ∈ B → IsCompact (U : Set X))
variable (F : TopCat.Sheaf (Type u) X)

/- Lemma 17.19.2 (0CAI): every set-valued sheaf is a filtered colimit of finite
presentations relative to a basis of quasi-compact opens. -/
@[stacks 0CAI]
#check
  (TopCat.Sheaf.BasisPresentation.ind hB hcompact F :
    (TopCat.Sheaf.BasisPresentation.IsFinite B).ind F)

end

end
