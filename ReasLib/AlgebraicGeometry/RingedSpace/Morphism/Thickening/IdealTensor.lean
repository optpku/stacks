/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Morphism.Thickening.FirstOrder
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Monoidal

/-!
# Tensor comparisons of kernel ideals

A morphism of first-order thickenings induces a comparison of ideal tensor modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace (Modules)
open AlgebraicGeometry.RingedSpace.Hom
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening.Hom

variable {T U : Thickening.{u}} [IsFirstOrderThickening T.hom] [IsFirstOrderThickening U.hom]

/-- The canonical `𝒪_X`-map `f^* 𝒥 ⊗ F ⟶ ℐ ⊗ F` along a morphism of first-order
thickenings, obtained by tensoring `sourceIdealMap` with `F`. -/
def sourceIdealTensorMap (g : T ⟶ U) (F : T.left.Modules) :
    (g.left ^*).obj (RingedSpace.Hom.idealModule U.hom) ⊗ F ⟶
      RingedSpace.Hom.idealModule T.hom ⊗ F :=
  tensorHom (sourceIdealMap g) (𝟙 F)

/-- `sourceIdealTensorMap` is the tensor morphism of `sourceIdealMap` with `𝟙 F`. -/
theorem sourceIdealTensorMap_eq (g : T ⟶ U) (F : T.left.Modules) :
    sourceIdealTensorMap g F = tensorHom (sourceIdealMap g) (𝟙 F) := sorry

end AlgebraicGeometry.RingedSpace.Thickening.Hom
