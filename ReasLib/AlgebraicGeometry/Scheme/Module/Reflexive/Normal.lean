/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.LocallyFree
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Approximation
public import ReasLib.AlgebraicGeometry.Scheme.Module.Depth
public import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive
public import ReasLib.AlgebraicGeometry.Scheme.Module.Torsion
public import ReasLib.AlgebraicGeometry.Scheme.Normal

/-!
# Reflexive modules on normal schemes

This file relates reflexivity of a coherent module on a normal scheme to Serre's condition
and extension from a finite-locally-free restriction across a codimension-two complement.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
variable (ℱ : X.Modules) [ℱ.IsCoherent]

/-- On an integral locally Noetherian normal scheme, a coherent module is reflexive exactly
when it is torsion-free and satisfies `(S₂)`, and exactly when it is finite locally free on an
open with codimension-at-least-two complement and the canonical map to the pushforward of its
restriction is an isomorphism. -/
theorem isReflexive_tfae_torsionFree_serreS2_codimTwoOpen
    (hXnormal : X.isNormal) :
    List.TFAE
      [ IsReflexive ℱ,
        IsTorsionFree ℱ ∧ satisfiesSerreConditionS ℱ 2,
        ∃ U : X.Opens,
          Scheme.IdealSheafData.irreducibleComponentsCodimAtLeast
              2 ((U : Set X)ᶜ : Set X) ∧
            SheafOfModules.IsFiniteLocallyFree
              ((Scheme.Modules.pullback U.ι).obj ℱ) ∧
            IsIso ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app ℱ)
      ] := sorry

end AlgebraicGeometry.Scheme.Modules
