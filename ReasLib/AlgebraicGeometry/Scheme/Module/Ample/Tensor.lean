/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- If the positive tensor-power nonvanishing opens of an invertible module `M` cover a scheme,
then tensoring an ample invertible module `L` with `M` preserves ampleness. -/
theorem isAmple_tensor_of_isAmple_of_nonvanishing_cover
    (L M : X.Modules) [hL : Invertible L] [hM : Invertible M] [IsAmple L]
    (hcover : ∀ x : X, ∃ m : ℕ, 0 < m ∧
      ∃ t : Γ(RingedSpace.TensorPower.sheaf M m, ⊤),
        x ∈ (hM.nonvanishingOpen t : Set X)) :
    IsAmple (L ⊗ M) := sorry

end AlgebraicGeometry.Scheme.Modules
