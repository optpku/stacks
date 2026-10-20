/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.Injectivity
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 31.5.10: let `X` be a scheme and let `φ : ℱ ⟶ 𝒢` be a morphism of quasicoherent
modules. If at every point either the induced stalk map is injective or the point is not weakly
associated to `ℱ`, then `φ` is a monomorphism. -/
@[stacks 0AVP] #check
  (AlgebraicGeometry.Scheme.Modules.mono_of_stalkwise_injective_or_not_mem_weakAss :
    ∀ {X : Scheme.{u}} {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]
      (φ : ℱ ⟶ 𝒢),
      (∀ x : X,
        Function.Injective (RingedSpace.moduleStalkHom x φ) ∨ x ∉ ℱ.weakAss) → Mono φ)
