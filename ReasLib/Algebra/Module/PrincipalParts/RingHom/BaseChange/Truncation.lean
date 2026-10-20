/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.PrincipalParts.RingHom.BaseChange
public import ReasLib.Algebra.Module.PrincipalParts.RingHom.Truncation

/-!
# Base change and order truncation for explicit ring homomorphisms

This file records the compatibility between the two structural maps of principal parts: change
of a commuting ring square and truncation of the order bound.  Presheaf and sheaf constructions
can reuse this law objectwise without rebuilding scalar actions.

@stack 09CP
-/

@[expose] public section

open CategoryTheory

universe u

noncomputable section

namespace PrincipalParts.RingHom.BaseChange

variable {A B A' B' : Type u}
variable [CommRing A] [CommRing B] [CommRing A'] [CommRing B']

/-- Explicit base change of principal parts commutes with truncation of the order bound. -/
@[stacks 09CP "base change commutes with truncation"]
theorem map_truncate (σ : A →+* B) (σ' : A' →+* B') (a : A →+* A') (b : B →+* B')
    (sq : b.comp σ = σ'.comp a) {k l : ℕ} (h : k ≤ l)
    {M : ModuleCat.{u} B} {M' : ModuleCat.{u} B'}
    (f : M ⟶ (ModuleCat.restrictScalars b).obj M') :
    map σ σ' a b sq l f ≫
        (ModuleCat.restrictScalars b).map (PrincipalParts.RingHom.truncate σ' M' h) =
      PrincipalParts.RingHom.truncate σ M h ≫ map σ σ' a b sq k f := sorry

end PrincipalParts.RingHom.BaseChange

end
