/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.DescentData.Pullback

open CategoryTheory

universe u v w

#check
  (@AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData.Pullback.functorOfHom :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {U V : AlgebraicGeometry.AlgebraicSpace S}
      {I : Type v} {J : Type w}
      {Uᵢ : I → AlgebraicGeometry.AlgebraicSpace S}
      {Vⱼ : J → AlgebraicGeometry.AlgebraicSpace S}
      {u : ∀ i, Uᵢ i ⟶ U} {v : ∀ j, Vⱼ j ⟶ V}
      {base : U ⟶ V}
      (α : I → J) (gᵢ : ∀ i, Uᵢ i ⟶ Vⱼ (α i))
      (comm : ∀ i, gᵢ i ≫ v (α i) = u i ≫ base),
      AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData Vⱼ v ⥤
        AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData Uᵢ u)

#check
  (@AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData.Pullback.isoOfHom :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {U V : AlgebraicGeometry.AlgebraicSpace S}
      {I : Type v} {J : Type w}
      {Uᵢ : I → AlgebraicGeometry.AlgebraicSpace S}
      {Vⱼ : J → AlgebraicGeometry.AlgebraicSpace S}
      {u : ∀ i, Uᵢ i ⟶ U} {v : ∀ j, Vⱼ j ⟶ V}
      {base : U ⟶ V}
      (α : I → J) (gᵢ : ∀ i, Uᵢ i ⟶ Vⱼ (α i))
      (comm : ∀ i, gᵢ i ≫ v (α i) = u i ≫ base)
      (α' : I → J) (gᵢ' : ∀ i, Uᵢ i ⟶ Vⱼ (α' i))
      (comm' : ∀ i, gᵢ' i ≫ v (α' i) = u i ≫ base),
      AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData.Pullback.functorOfHom α gᵢ comm ≅
        AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData.Pullback.functorOfHom α' gᵢ' comm')
