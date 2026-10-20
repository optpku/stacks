/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.Support
public import ReasLib.AlgebraicGeometry.Scheme.WeaklyAssociatedPoints.GenericPoints
import StacksCheckRecall

universe u

/- Lemma 31.5.7 (1): every minimal specialization point of the support of a quasicoherent
scheme module is weakly associated to the module. -/
@[stacks 05AQ] #check
  (@AlgebraicGeometry.Scheme.Modules.minimalSpecializationPoints_support_subset_weakAss :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (ℱ : X.Modules) [ℱ.IsQuasicoherent],
      X.minimalSpecializationPoints
        (AlgebraicGeometry.Scheme.Modules.moduleSupport ℱ) ⊆ ℱ.weakAss)

/- Lemma 31.5.7 (2): every generic point of an irreducible component of a scheme is weakly
associated to its structure sheaf. -/
@[stacks 05AQ] #check (AlgebraicGeometry.Scheme.genericPoints_subset_weakAss :
  ∀ (X : AlgebraicGeometry.Scheme.{u}),
    genericPoints X ⊆ X.weakAss)
