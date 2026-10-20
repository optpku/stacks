/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Depth
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped ENat

universe u

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
variable (ℱ : X.Modules) [ℱ.IsCoherent]
variable (x : X) (k : ℕ)

/- Definition 30.11.1: A coherent module on a locally Noetherian scheme satisfies
Serre's condition `(S_k)` exactly when every stalk has depth at least the minimum of `k`
and the dimension of its support.
-/
@[stacks 0341] #check (AlgebraicGeometry.Scheme.Modules.satisfiesSerreConditionS_iff ℱ k :
    AlgebraicGeometry.Scheme.Modules.satisfiesSerreConditionS ℱ k ↔
      ∀ x : X,
        WithBot.some
            (moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) : ℕ∞) ≥
          min (k : WithBot ℕ∞)
            (Module.supportDim (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x)))

#check (AlgebraicGeometry.Scheme.Modules.hasDepthAt_iff ℱ x k :
    AlgebraicGeometry.Scheme.Modules.hasDepthAt ℱ x k ↔
      moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) = k)

#check (AlgebraicGeometry.Scheme.hasDepthAt_iff X x k :
    AlgebraicGeometry.Scheme.hasDepthAt X x k ↔
      moduleDepth (X.presheaf.stalk x) (X.presheaf.stalk x) = k)

#check (AlgebraicGeometry.Scheme.satisfiesSerreConditionS_iff_structureSheaf X k :
    AlgebraicGeometry.Scheme.satisfiesSerreConditionS X k ↔
      AlgebraicGeometry.Scheme.Modules.satisfiesSerreConditionS
        (ℱ := (SheafOfModules.unit X.ringCatSheaf : X.Modules)) k)
