/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.Basic
public import ReasLib.RingTheory.CohenMacaulay.SerreCondition

/-!
# Stalkwise depth conditions for module sheaves

This leaf owns pointwise depth and Serre `(S_k)` predicates for modules on a
locally ringed space. Scheme-level finiteness bridges belong in the scheme
specialization layer.
-/

@[expose] public section

open AlgebraicGeometry
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.LocallyRingedSpace.Modules

variable {X : LocallyRingedSpace.{u}}

/-- A module sheaf has finite stalks when every stalk is finite over the corresponding local
ring. This is the exact finiteness input required by the depth construction. -/
class HasFiniteStalks (ℱ : X.Modules) : Prop where
  /-- Every stalk of the module is finite over its local ring. -/
  module_finite (x : X) :
    Module.Finite (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x)

namespace HasFiniteStalks

/-- A finite-stalks hypothesis supplies the finite module instance at each point. -/
instance moduleFinite
    (ℱ : X.Modules) [HasFiniteStalks ℱ] (x : X) :
    Module.Finite (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) :=
  HasFiniteStalks.module_finite x

end HasFiniteStalks

/-- A module has depth `k` at a point when the depth of its stalk over the local stalk ring is
equal to `k`. -/
abbrev hasDepthAt
    (ℱ : X.Modules) [HasFiniteStalks ℱ] (x : X) (k : ℕ) : Prop :=
  moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) = k

/-- The pointwise depth predicate unfolds to the depth of the stalk module. -/
@[simp]
theorem hasDepthAt_iff
    (ℱ : X.Modules) [HasFiniteStalks ℱ] (x : X) (k : ℕ) :
    hasDepthAt ℱ x k ↔
      moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) = k := sorry

/-- A module satisfies Serre's condition `(S_k)` when every stalk has depth at least the minimum
of `k` and the dimension of its support. -/
abbrev satisfiesSerreConditionS
    (ℱ : X.Modules) [HasFiniteStalks ℱ] (k : ℕ) : Prop :=
  ∀ x : X,
    WithBot.some (moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) : ℕ∞) ≥
      min (k : WithBot ℕ∞)
        (Module.supportDim (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x))

/-- The stalkwise Serre condition unfolds to its local depth inequalities. -/
@[simp]
theorem satisfiesSerreConditionS_iff
    (ℱ : X.Modules) [HasFiniteStalks ℱ] (k : ℕ) :
    satisfiesSerreConditionS ℱ k ↔
      ∀ x : X,
        WithBot.some (moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) : ℕ∞) ≥
          min (k : WithBot ℕ∞)
            (Module.supportDim (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x)) := sorry

end AlgebraicGeometry.LocallyRingedSpace.Modules
