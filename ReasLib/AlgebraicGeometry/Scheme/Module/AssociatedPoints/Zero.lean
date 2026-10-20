/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.Zero
public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.FiniteGeneration

/-!
# Vanishing of scheme modules and associated points

A quasicoherent module on a locally Noetherian scheme vanishes exactly when its associated-point
locus is empty.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A quasicoherent module on a locally Noetherian scheme is zero if and only if its associated-point
locus is empty. -/
theorem isZero_iff_associatedPoints_eq_empty {X : Scheme.{u}} (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] [IsLocallyNoetherian X] :
    IsZero ℱ ↔ associatedPoints ℱ = (∅ : Set X) := by
  rw [associatedPoints_eq_weakAss_of_isLocallyNoetherian ℱ]
  exact isZero_iff_weakAss_eq_empty ℱ

/-- A quasicoherent module on a locally Noetherian scheme is zero if and only if none of its points
is associated to it. -/
theorem isZero_iff_forall_not_mem_associatedPoints {X : Scheme.{u}} (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] [IsLocallyNoetherian X] :
    IsZero ℱ ↔ ∀ x : X, x ∉ associatedPoints ℱ := by
  constructor
  · intro hzero x hx
    have hEmpty : associatedPoints ℱ = (∅ : Set X) :=
      (isZero_iff_associatedPoints_eq_empty ℱ).1 hzero
    have : x ∈ (∅ : Set X) := by simpa [hEmpty] using hx
    simpa using this
  · intro h
    apply (isZero_iff_associatedPoints_eq_empty ℱ).2
    ext x
    constructor
    · intro hx
      exact False.elim <| h x hx
    · intro hx
      cases hx

end AlgebraicGeometry.Scheme.Modules
