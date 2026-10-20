/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.AssociatedPoints.GenericPoints
import StacksCheckRecall

universe u

/- Lemma 31.2.9 (1): for a quasi-coherent module on a locally Noetherian scheme, every point
minimal under specialization in the support is an associated point of the module. -/
@[stacks 05AH] #check
  (AlgebraicGeometry.Scheme.Modules.minimalSpecializationPoints_support_subset_associatedPoints :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent],
      X.minimalSpecializationPoints
          (AlgebraicGeometry.RingedSpace.moduleSupport ℱ) ⊆
        AlgebraicGeometry.Scheme.Modules.associatedPoints ℱ)

/- Lemma 31.2.9 (2): every generic point of an irreducible component of a locally Noetherian
scheme is an associated point of its structure sheaf. -/
@[stacks 05AH] #check
  (AlgebraicGeometry.Scheme.genericPoints_subset_associatedPoints :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsLocallyNoetherian X],
      genericPoints X ⊆ X.associatedPoints)
