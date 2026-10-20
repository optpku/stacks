/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaf.Torsor
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u

namespace CategoryTheory.Sheaf.Torsor

variable {X : TopCat.{u}} {G : X.Sheaf GrpCat.{u}}

/- Lemma 20.4.2 (02FP): a `G`-torsor on `X` is trivial if and only if it has a
section over the canonical top open. -/
@[stacks 02FP]
#check @isTrivial_iff_nonempty_sections_top

#check @nonempty_globalSections_iff_nonempty_sections_top
#check @isTrivial_iff_nonempty_globalSections

end CategoryTheory.Sheaf.Torsor
