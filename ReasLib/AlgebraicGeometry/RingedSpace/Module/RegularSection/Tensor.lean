/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.RegularSection
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorUnit

/-!
# Tensor multiplication by a section

This file defines the morphism on a module sheaf induced by tensoring with a global section of
another module sheaf.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/-- The morphism `ℱ ⟶ ℱ ⊗ ℒ` induced by tensoring with a global section of `ℒ`. -/
noncomputable abbrev tensorSectionHom (ℱ ℒ : X.Modules) (s : ℒ.sections) : ℱ ⟶ ℱ ⊗ ℒ :=
  (ρ_ ℱ).inv ≫
    (𝟙 ℱ ⊗ₘ (tensorUnitToUnitModule X ≫ regularSectionHom ℒ s))

end AlgebraicGeometry.RingedSpace
