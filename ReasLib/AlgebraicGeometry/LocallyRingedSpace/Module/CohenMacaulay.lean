/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.Depth
public import ReasLib.RingTheory.CohenMacaulay.Module

/-!
# Cohen-Macaulay module sheaves on locally ringed spaces

This leaf owns the stalkwise Cohen-Macaulay predicate under the exact ambient
hypothesis required by the local algebra: Noetherian stalk rings.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.LocallyRingedSpace.Modules

variable {X : LocallyRingedSpace.{u}}
variable [∀ x : X, IsNoetherianRing (X.presheaf.stalk x)]

/-- A module sheaf on a locally ringed space is Cohen-Macaulay when each
stalk is a Cohen-Macaulay module over its local stalk ring. -/
class CohenMacaulay (ℱ : X.Modules) : Prop extends HasFiniteStalks ℱ where
  /-- A stalk is zero or is Cohen-Macaulay in the nonzero local-module convention. -/
  stalk (x : X) :
    Subsingleton (RingedSpace.stalkModuleCat ℱ x) ∨
      Module.CohenMacaulay (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x)

namespace CohenMacaulay

/-- A stalk of a Cohen-Macaulay module sheaf is a Cohen-Macaulay module. -/
theorem stalk_cohenMacaulay
    (ℱ : X.Modules) [CohenMacaulay ℱ] (x : X)
    [Nontrivial (RingedSpace.stalkModuleCat ℱ x)] :
    Module.CohenMacaulay (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) := sorry

/-- A Cohen-Macaulay module sheaf supplies the Cohen-Macaulay instance at every stalk. -/
instance instStalkCohenMacaulay
    (ℱ : X.Modules) [CohenMacaulay ℱ] (x : X)
    [Nontrivial (RingedSpace.stalkModuleCat ℱ x)] :
    Module.CohenMacaulay (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) :=
  stalk_cohenMacaulay ℱ x

/-- A Cohen-Macaulay module sheaf has finite stalks. -/
theorem hasFiniteStalks
    (ℱ : X.Modules) [CohenMacaulay ℱ] :
    HasFiniteStalks ℱ := CohenMacaulay.toHasFiniteStalks

/-- A Cohen-Macaulay module sheaf supplies the finite-stalks instance needed by stalkwise depth
and Serre-condition APIs. -/
instance instHasFiniteStalks
    (ℱ : X.Modules) [CohenMacaulay ℱ] :
    HasFiniteStalks ℱ :=
  hasFiniteStalks ℱ

theorem of_subsingleton_stalks (ℱ : X.Modules)
    (h : ∀ x : X, Subsingleton (RingedSpace.stalkModuleCat ℱ x)) :
    CohenMacaulay ℱ := by
  refine { toHasFiniteStalks := ?_, stalk := fun x ↦ Or.inl (h x) }
  exact ⟨fun x ↦ by letI := h x; infer_instance⟩

end CohenMacaulay

/-- A module sheaf is Cohen-Macaulay exactly when every stalk satisfies the local algebraic
Serre condition `(S_k)` for every natural number `k`. -/
theorem cohenMacaulay_iff_forall_serreConditionS
    (ℱ : X.Modules) :
    CohenMacaulay ℱ ↔
      ∀ x : X, ∀ k : ℕ,
        Module.SerreConditionS (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) k := sorry

/-- A module sheaf is Cohen-Macaulay exactly when it satisfies every named stalkwise
Serre-condition predicate. -/
theorem cohenMacaulay_iff_forall_satisfiesSerreConditionS
    (ℱ : X.Modules) [HasFiniteStalks ℱ] :
    CohenMacaulay ℱ ↔ ∀ k : ℕ, satisfiesSerreConditionS ℱ k := sorry

end AlgebraicGeometry.LocallyRingedSpace.Modules
