/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-! # Self-extensions and first group cohomology -/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace Rep

/-- Representations admit derived Ext groups in the standard universe. -/
instance instHasExt (k Γ : Type u) [Field k] [Group Γ] : HasExt.{u + 1} (Rep.{u} k Γ) :=
  HasExt.standard (Rep.{u} k Γ)

end Rep

namespace groupCohomology

/-- Extensions of representations with finite-dimensional source are classified linearly
by first cohomology with the linear-homomorphism coefficient representation. -/
theorem nonempty_extIsoH1 {k Γ : Type u} [Field k] [Group Γ]
    (X Y : Rep.{u} k Γ) [FiniteDimensional k X.V] :
    Nonempty ((Abelian.Ext.{u + 1} X Y 1) ≃ₗ[k]
      groupCohomology.H1 (Rep.of (Representation.linHom X.ρ Y.ρ))) := sorry

end groupCohomology
