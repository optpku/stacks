/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Properties
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.TFAE
import ReasLib.RingTheory.Flatness.LocallyFree.Reduced

/-!
# Reduced-scheme finite local freeness criteria

On a reduced scheme, the stalkwise-freeness clause can be omitted from the finite-local-freeness
criterion.  This leaf adds exactly that reducedness refinement.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- A scheme module of finite type whose named fiber-rank function is locally constant. -/
class FiniteTypeRankLocallyConstant (ℱ : X.Modules) : Prop extends
    ℱ.IsFiniteType,
    IsFiberRankLocallyConstant ℱ

/-- Finite type and locally constant fiber rank canonically give their combined condition. -/
instance instFiniteTypeRankLocallyConstant {ℱ : X.Modules}
    [ℱ.IsFiniteType] [IsFiberRankLocallyConstant ℱ] :
    FiniteTypeRankLocallyConstant ℱ := sorry

/-- The finite-type locally-constant-rank condition is equivalent to its two constituents. -/
theorem finiteTypeRankLocallyConstant_iff (ℱ : X.Modules) :
    FiniteTypeRankLocallyConstant ℱ ↔
      ℱ.IsFiniteType ∧ IsFiberRankLocallyConstant ℱ := sorry

/-- On a reduced scheme, finite type with locally constant fiber rank is equivalent to finite
local freeness for quasi-coherent modules. -/
theorem finiteTypeRankLocallyConstant_iff_isFiniteLocallyFree_of_isReduced
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] [IsReduced X] :
    FiniteTypeRankLocallyConstant ℱ ↔
      SheafOfModules.IsFiniteLocallyFree ℱ := sorry

/-- On a reduced scheme, the standard finite-local-freeness conditions for a quasi-coherent
module are also equivalent to finite type with locally constant fiber rank. -/
@[stacks 0FWH]
theorem finiteLocallyFree_tfae_of_isReduced
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] [IsReduced X] :
    List.TFAE [
      FinitePresentationFlat ℱ,
      FinitePresentationStalkwiseFree ℱ,
      LocallyFreeFiniteType ℱ,
      SheafOfModules.IsFiniteLocallyFree ℱ,
      FiniteTypeStalkwiseFreeRankLocallyConstant ℱ,
      FiniteTypeRankLocallyConstant ℱ
    ] := sorry

end AlgebraicGeometry.Scheme.Modules
