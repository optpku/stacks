/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.FlatBaseChange.DirectImage
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Coreflector

/-! # Quasi-coherent direct image of algebraic stacks -/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped Bicategory

noncomputable section
universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

namespace QCoh

/-- Quasi-coherent direct image is inclusion into flat-base-change modules,
étale direct image, and the quasi-coherent coreflector. The supplied section
smallness is the size convention for the original coefficient universe. -/
def directImage {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallCFGTypeSections f] : QCoh X ⥤ QCoh Y :=
  toLQCohFbc X ⋙ LQCohFbc.directImage f ⋙ LQCohFbc.toQCoh Y

/-- Quasi-coherent direct image is the displayed inclusion, direct-image,
and coreflector composite. -/
theorem directImage_eq {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallCFGTypeSections f] :
    directImage f = toLQCohFbc X ⋙ LQCohFbc.directImage f ⋙ LQCohFbc.toQCoh Y := rfl

/-- Quasi-coherent direct image is additive. -/
instance directImage_additive {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallCFGTypeSections f] : (directImage f).Additive := sorry

end QCoh
end AlgebraicGeometry.GroupoidsOver
