/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.QCoh

/-- The tensor unit of `X.Modules` is quasicoherent. -/
instance tensorUnit_isQuasicoherent (X : Scheme.{u}) :
    (𝟙_ X.Modules).IsQuasicoherent := sorry

/-- The structure sheaf `O_X` as an object of `Scheme.QCoh X`. -/
noncomputable def structureSheaf (X : Scheme.{u}) : Scheme.QCoh X :=
  ⟨𝟙_ X.Modules, tensorUnit_isQuasicoherent X⟩

/-- The underlying module of `structureSheaf X` is the tensor unit of `X.Modules`. -/
theorem structureSheaf_obj (X : Scheme.{u}) :
    (structureSheaf X).obj = 𝟙_ X.Modules := sorry

end AlgebraicGeometry.Scheme.QCoh
