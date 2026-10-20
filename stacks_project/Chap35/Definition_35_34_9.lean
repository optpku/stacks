/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.DescentData.Pullback.Family
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u v w

variable {S S' : Scheme.{u}}
variable {𝒰 : SemiRepresentableFamily.Over.{v} S'}
variable {𝒱 : SemiRepresentableFamily.Over.{w} S}
variable {base : S' ⟶ S}

/- Definition 35.34.9: the componentwise functor constructed in Lemma 35.34.8, sending
scheme descent data on a target family to its pullback along a morphism of families, is the
pullback functor on descent data. -/
@[stacks 02VT] #check
  (AlgebraicGeometry.Scheme.DescentData.Pullback.functorOfHom (base := base) :
    (φ : SemiRepresentableFamily.Over.Hom
      (SemiRepresentableFamily.Over.map (Over.map base) 𝒰) 𝒱) →
      Scheme.DescentData
          (fun j ↦ (𝒱.obj j).left) (fun j ↦ (𝒱.obj j).hom) ⥤
        Scheme.DescentData
          (fun i ↦ (𝒰.obj i).left) (fun i ↦ (𝒰.obj i).hom))
