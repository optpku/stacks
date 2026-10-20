/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.Basic
import StacksCheckRecall

/-!
# Structure sheaf and module category of an algebraic space

@stack 03G7

The public owner supplies the actual global-section presheaf, its sheaf,
the small étale ringed site, and the category of module sheaves.
-/

@[expose] public section

@[stacks 03G7 "structure sheaf"]
#check @AlgebraicGeometry.AlgebraicSpace.structureSheaf

@[stacks 03G7 "sections on an étale scheme"]
#check @AlgebraicGeometry.AlgebraicSpace.structureSheaf_obj

#check @AlgebraicGeometry.AlgebraicSpace.structurePresheaf
#check @AlgebraicGeometry.AlgebraicSpace.structurePresheaf_map
#check @AlgebraicGeometry.AlgebraicSpace.structurePresheaf_isSheaf
#check @AlgebraicGeometry.AlgebraicSpace.ringedSite
#check @AlgebraicGeometry.AlgebraicSpace.ringedSite_structureSheaf
#check @AlgebraicGeometry.AlgebraicSpace.Modules
#check @AlgebraicGeometry.AlgebraicSpace.Modules_eq
