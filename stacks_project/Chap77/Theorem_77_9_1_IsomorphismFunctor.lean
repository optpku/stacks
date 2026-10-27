/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.BaseChange.IsomorphismOverSFunctor

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
variable {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]
variable (u : ℱ ⟶ 𝒢)

/- Theorem 77.9.1: The isomorphism functor on schemes over `S` records maps to `B`
along which the base change of the module morphism is invertible. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.isomorphismOverSFunctor f u :
  (Over S)ᵒᵖ ⥤ Type u)
