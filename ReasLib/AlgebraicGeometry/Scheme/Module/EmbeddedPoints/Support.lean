/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Support
public import ReasLib.AlgebraicGeometry.Scheme.Module.EmbeddedPoints
public import ReasLib.AlgebraicGeometry.Scheme.Module.Support

/-!
# Embedded associated points and module support

This file characterizes embedded associated points using the points minimal
under specialization in the support of a scheme module.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

namespace embeddedAssociatedAt

/-- For a finite-type quasi-coherent module on a locally Noetherian scheme, a point is embedded
associated exactly when it is associated but not minimal under specialization in the support. -/
theorem iff_mem_associatedPoints_and_not_minimal
    [IsLocallyNoetherian X] (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (x : X) :
    ℱ.embeddedAssociatedAt x ↔
      x ∈ associatedPoints ℱ ∧
        x ∉ X.minimalSpecializationPoints (RingedSpace.moduleSupport ℱ) := sorry

end embeddedAssociatedAt

end AlgebraicGeometry.Scheme.Modules
