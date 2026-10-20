/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

@[expose] public section
open CategoryTheory
noncomputable section
universe u v w

namespace ActualModuleRestriction

/-- Rebundle a specified additive equivalence with its actual restriction-of-scalars law. -/
def restrictionIso {A : Type u} {B : Type v} [Ring A] [Ring B] (h : A →+* B)
    (N : ModuleCat.{w} B) (M : ModuleCat.{w} A) (e : N ≃+ M)
    (he : ∀ (a : A) (x : N), e (h a • x) = a • e x) :
    (ModuleCat.restrictScalars h).obj N ≅ M :=
  -- Local instance justification (defeq pin): exactly the source action of restrictScalars h.
  letI := Module.compHom N h
  (show (ModuleCat.restrictScalars h).obj N ≃ₗ[A] M from
    { __ := e
      map_smul' := he }).toModuleIso

end ActualModuleRestriction
