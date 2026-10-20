/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent
import StacksCheckRecall

@[expose] public section

open CategoryTheory.Sheaf

/- Equation 18.35.0.1: the canonical presentation `𝒜[𝒝] ⟶ 𝒝`
evaluates the bracket generator `[b]` at the section `b`. -/
@[stacks 08TU]
#check @FreeAlgebra.Presentation.generator_map

#check @FreeAlgebra.Presentation.obj
#check @FreeAlgebra.Presentation.hom
#check @FreeAlgebra.Presentation.map
#check @FreeAlgebra.Presentation.generator
#check @FreeAlgebra.Presentation.underlying
#check @FreeAlgebra.Presentation.base
