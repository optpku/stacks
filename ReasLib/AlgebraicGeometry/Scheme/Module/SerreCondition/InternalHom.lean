/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Depth.InternalHom

/-!
# Serre conditions for internal Hom

This file gives preservation results for the first two Serre conditions under internal Hom of
coherent modules on a locally Noetherian scheme.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
variable {ℱ 𝒢 : X.Modules} [ℱ.IsCoherent] [𝒢.IsCoherent]

/-- The internal Hom from a coherent module to a coherent module satisfying Serre's condition
`(S₁)` also satisfies `(S₁)` on a locally Noetherian scheme. -/
theorem satisfiesSerreConditionS_one_internalHom_of_satisfiesSerreConditionS_one
    (h𝒢 : satisfiesSerreConditionS 𝒢 1) :
    satisfiesSerreConditionS ((ihom ℱ).obj 𝒢) 1 := sorry

/-- The internal Hom from a coherent module to a coherent module satisfying Serre's condition
`(S₂)` also satisfies `(S₂)` on a locally Noetherian scheme. -/
theorem satisfiesSerreConditionS_two_internalHom_of_satisfiesSerreConditionS_two
    (h𝒢 : satisfiesSerreConditionS 𝒢 2) :
    satisfiesSerreConditionS ((ihom ℱ).obj 𝒢) 2 := sorry

end AlgebraicGeometry.Scheme.Modules
