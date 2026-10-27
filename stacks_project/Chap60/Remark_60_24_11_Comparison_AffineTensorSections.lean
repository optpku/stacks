/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.Scheme.Module.AffineSections
public import stacks_project.Chap60.Remark_60_24_11_Comparison_DeRham

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
namespace CrystallineAffineTensorSections
export AlgebraicGeometry.Scheme.Modules.Affine (tensorMap tensorMap_bijective tensorEquiv exteriorMap exteriorMap_bijective exteriorEquiv)
end CrystallineAffineTensorSections
open scoped TensorProduct
variable {Y : Scheme.{u}} (U : Y.affineOpens) (M N : Y.Modules)
#check (AlgebraicGeometry.Scheme.Modules.Affine.tensorMap U M N :
  Γ(M, U.1) ⊗[Γ(Y, U.1)] Γ(N, U.1) →ₗ[Γ(Y, U.1)]
    Γ(SheafOfModules.RingedSite.moduleTensor (𝒪 := Y.sheaf) M N, U.1))
