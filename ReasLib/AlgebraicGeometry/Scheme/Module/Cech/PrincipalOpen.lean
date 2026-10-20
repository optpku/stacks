/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.Ordered

/-!
# Principal-open module-valued Čech complexes

This module specializes the ordered module-valued Čech complex to a finite family of principal
opens of a scheme.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme.ModuleCech.Ordered

noncomputable section

universe u

namespace ModuleCech

variable {X : Scheme.{u}}

/-- The bounded extended alternating Čech complex associated to the principal opens
`X.basicOpen (f i)` and a module sheaf `ℱ`, with `ℱ` in degree zero. -/
abbrev ofSections {c : ℕ} (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) :
    CochainComplex X.Modules ℕ :=
  extended (fun i : ULift.{u} (Fin c) ↦ X.basicOpen (f i.down)) ℱ

/-- Degree zero of the principal-open extended Čech complex is the original module sheaf. -/
theorem ofSections_X_zero {c : ℕ} (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) :
    (ofSections f ℱ).X 0 = ℱ := sorry

/-- Degree `p + 1` of the principal-open extended Čech complex is the finite biproduct indexed by
strictly increasing `(p + 1)`-tuples. -/
theorem ofSections_X_succ {c : ℕ} (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) (p : ℕ) :
    (ofSections f ℱ).X (p + 1) =
      term (fun i : ULift.{u} (Fin c) ↦ X.basicOpen (f i.down)) ℱ p := sorry

/-- Every degree strictly above the number of principal opens is zero. -/
theorem ofSections_isZero_of_lt {c n : ℕ} (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules)
    (h : c < n) :
    IsZero ((ofSections f ℱ).X n) := sorry

end ModuleCech

end
