/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.BaseChange.IsomorphismFunctor

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

variable {S X : Scheme.{u}} (f : X ⟶ S)
variable {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]
variable (u : ℱ ⟶ 𝒢)

/- This typed check preserves the historical import surface while the implementation is owned
by the reusable base-change module. -/
#check (AlgebraicGeometry.Scheme.Modules.isomorphismFunctor f u : (Over S)ᵒᵖ ⥤ Type u)
