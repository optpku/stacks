/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive.Depth
import StacksCheckRecall

open AlgebraicGeometry
open scoped ENat

universe u

/- Lemma 31.12.10: let `X` be an integral locally Noetherian scheme and let `ℱ` be a coherent
`𝒪_X`-module. Then `ℱ` is reflexive if and only if, for every point `x : X`, either the stalk
`ℱ_x` is reflexive or it has depth at least two. -/
@[stacks 0AY5] #check
  (AlgebraicGeometry.Scheme.Modules.isReflexive_iff_stalk_isReflexive_or_moduleDepth_ge_two :
    ∀ {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
      (ℱ : X.Modules) [ℱ.IsCoherent],
      AlgebraicGeometry.Scheme.Modules.IsReflexive ℱ ↔
        ∀ x : X,
          Module.IsReflexive (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) ∨
            (2 : ℕ∞) ≤
              moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x))
