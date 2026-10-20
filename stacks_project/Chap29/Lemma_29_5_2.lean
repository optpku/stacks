/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Support
import StacksCheckRecall

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 29.5.2: The support of a quasi-coherent module sheaf on a scheme is closed under
specialization. -/
@[stacks 05AC] #check
  (AlgebraicGeometry.Scheme.Modules.stableUnderSpecialization_moduleSupport :
    ∀ {X : Scheme.{u}} (ℱ : X.Modules) [ℱ.IsQuasicoherent],
      StableUnderSpecialization (AlgebraicGeometry.RingedSpace.moduleSupport ℱ))
