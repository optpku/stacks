/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Support
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Exercise 111.36.3: on a scheme `X`, if `F` is a quasi-coherent `𝒪_X`-module,
`x` is a specialization of `x'` (that is, `x' ⤳ x`), and the stalk of `F` at
`x'` is nonzero, then the stalk of `F` at `x` is nonzero. -/
@[stacks 029Q] #check
  (AlgebraicGeometry.Scheme.Modules.stableUnderSpecialization_moduleSupport :
    ∀ {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent],
      StableUnderSpecialization (AlgebraicGeometry.Scheme.Modules.moduleSupport F))

end AlgebraicGeometry.Scheme.Modules
