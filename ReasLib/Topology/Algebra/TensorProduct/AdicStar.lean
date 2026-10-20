/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Algebra.Algebra
public import ReasLib.Topology.Algebra.TensorProduct.Admissibility
public import ReasLib.RingTheory.Topology.AdicStar

/-!
# Adic* completed tensors

Completed tensors of objects of `WAdm^{adic*}` remain in `WAdm^{adic*}`, so
`Completed B A C` is an object of `WAdm^{adic*}` when `A` and `C` are.
-/

@[expose] public section

noncomputable section

universe u

open TopologicalRing

namespace Algebra.TensorProduct.Completed

variable {B A C : Type u}
variable [CommRing B] [CommRing A] [CommRing C]
variable [Algebra B A] [Algebra B C]
variable [TopologicalSpace B] [TopologicalSpace A] [TopologicalSpace C]
variable [IsAdicStarRing B] [IsAdicStarRing A] [IsAdicStarRing C]
variable [ContinuousSMul B A] [ContinuousSMul B C]

/-- If `A` and `C` are objects of `WAdm^{adic*}`, then so is
`Completed B A C`. -/
instance instIsAdicStarRing : IsAdicStarRing (Completed B A C) :=
  { toIsAdicRing :=
      isAdicRing (continuous_algebraMap B A) (continuous_algebraMap B C)
        IsAdicStarRing.exists_fg_isIdealOfDefinition
        IsAdicStarRing.exists_fg_isIdealOfDefinition
    exists_fg_isIdealOfDefinition :=
      exists_fg_isIdealOfDefinition (continuous_algebraMap B A)
        (continuous_algebraMap B C)
        IsAdicStarRing.exists_fg_isIdealOfDefinition
        IsAdicStarRing.exists_fg_isIdealOfDefinition }

end Algebra.TensorProduct.Completed
