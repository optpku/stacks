/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Pullback.Family

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w

variable {S S' : Scheme.{u}}
variable {𝒰 : SemiRepresentableFamily.Over.{v} S'}
variable {𝒱 : SemiRepresentableFamily.Over.{w} S}
variable {base : S' ⟶ S}

#check
  (AlgebraicGeometry.Scheme.DescentData.Pullback.functorOfHom (base := base) :
    (φ : SemiRepresentableFamily.Over.Hom
      (SemiRepresentableFamily.Over.map (Over.map base) 𝒰) 𝒱) →
      Scheme.DescentData
          (fun j ↦ (𝒱.obj j).left) (fun j ↦ (𝒱.obj j).hom) ⥤
        Scheme.DescentData
          (fun i ↦ (𝒰.obj i).left) (fun i ↦ (𝒰.obj i).hom))
