/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.Affine

/-!
# Vanishing of scheme modules and weakly associated points

A quasicoherent module on a scheme vanishes exactly when its weakly associated
locus is empty.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A quasicoherent module on a scheme is zero if and only if its weakly
associated locus is empty. -/
@[stacks 05AP]
theorem isZero_iff_weakAss_eq_empty {X : Scheme.{u}} (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] :
    IsZero ℱ ↔ ℱ.weakAss = (∅ : Set X) := sorry

/-- A quasicoherent module on a scheme is zero if and only if no point is
weakly associated to it. -/
theorem isZero_iff_forall_not_weaklyAssociatedAt {X : Scheme.{u}} (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] :
    IsZero ℱ ↔ ∀ x : X, ¬ ℱ.weaklyAssociatedAt x := sorry

end AlgebraicGeometry.Scheme.Modules
