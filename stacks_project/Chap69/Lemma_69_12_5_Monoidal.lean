/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Monoidal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.UniverseLift

/-! # Tensor and internal Hom of modules on algebraic spaces

The public owners retain canonical monoidal transport and actual lifted section data.
-/

@[expose] public section

#check @AlgebraicGeometry.AlgebraicSpace.commRingSheafIso
#check @AlgebraicGeometry.AlgebraicSpace.Modules.commModulesEquivalence
#check @AlgebraicGeometry.AlgebraicSpace.Modules.instMonoidalCategory
#check @AlgebraicGeometry.AlgebraicSpace.Modules.liftedSection
#check @AlgebraicGeometry.AlgebraicSpace.Modules.liftedSectionRestrict
#check @AlgebraicGeometry.AlgebraicSpace.Modules.liftModule
#check @AlgebraicGeometry.AlgebraicSpace.Modules.internalHom
