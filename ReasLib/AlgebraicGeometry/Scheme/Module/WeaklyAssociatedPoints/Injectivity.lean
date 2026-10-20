/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.ExactSequence
public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.Zero

/-!
# Injectivity from weakly associated points

This module gives a criterion for a morphism of quasicoherent modules on a scheme to be a
monomorphism by testing injectivity at weakly associated points.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}
variable {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]

/-- A morphism of quasicoherent modules is a monomorphism if its stalk map is injective at
every weakly associated point of its source. -/
theorem mono_of_stalkwise_injective_or_not_mem_weakAss
    (φ : ℱ ⟶ 𝒢)
    (hφ : ∀ x : X,
      Function.Injective (RingedSpace.moduleStalkHom x φ) ∨ x ∉ ℱ.weakAss) :
    Mono φ := sorry

end AlgebraicGeometry.Scheme.Modules
