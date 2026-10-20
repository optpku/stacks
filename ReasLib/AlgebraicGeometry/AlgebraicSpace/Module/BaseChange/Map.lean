/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage

/-!
# Base change of a module morphism on an algebraic space

Pulling a morphism of quasi-coherent modules on an algebraic space `X` back along the
projection `X ×_B T ⟶ X` associated to a test scheme `T` over `B`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
variable {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]

/-- The fibre product `X ×_B T` of an algebraic space `X` with a scheme `T` over `B`. -/
abbrev baseChangeSpace {T : Over S} (a : ofOver T ⟶ B) : AlgebraicSpace S :=
  Limits.pullback f a

/-- The projection `X ×_B T ⟶ X`. -/
abbrev baseChangeProj {T : Over S} (a : ofOver T ⟶ B) : baseChangeSpace f a ⟶ X :=
  Limits.pullback.fst f a

/-- The pullback of a module on `X` to `X ×_B T`. -/
abbrev baseChangeModule {T : Over S} (a : ofOver T ⟶ B) (ℱ : X.Modules) :
    (baseChangeSpace f a).Modules :=
  (pullback (Limits.pullback.fst f a)).obj ℱ

/-- `baseChangeModule f a ℱ` is module pullback of `ℱ` along `X ×_B T ⟶ X`. -/
theorem baseChangeModule_eq {T : Over S} (a : ofOver T ⟶ B) (ℱ : X.Modules) :
    baseChangeModule f a ℱ = (pullback (Limits.pullback.fst f a)).obj ℱ :=
  sorry

/-- The pullback `u_T` of a module morphism along `X ×_B T ⟶ X`. -/
def baseChangeMap {T : Over S} (a : ofOver T ⟶ B) (u : ℱ ⟶ 𝒢) :
    baseChangeModule f a ℱ ⟶ baseChangeModule f a 𝒢 :=
  (pullback (Limits.pullback.fst f a)).map u

/-- `baseChangeMap f a u` is the image of `u` under module pullback along `X ×_B T ⟶ X`. -/
theorem baseChangeMap_eq {T : Over S} (a : ofOver T ⟶ B) (u : ℱ ⟶ 𝒢) :
    baseChangeMap f a u = (pullback (Limits.pullback.fst f a)).map u :=
  sorry

/-- Invertibility of `u_T` is preserved by further base change along a morphism of schemes
over `S`. -/
theorem baseChangeMap_isIso_of_over {T T' : Over S} (a : ofOver T ⟶ B) (φ : T' ⟶ T)
    (u : ℱ ⟶ 𝒢) (h : IsIso (baseChangeMap f a u)) :
    IsIso (baseChangeMap f (ofOverMap φ ≫ a) u) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
