/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent
import StacksCheckRecall

/-!
# Lemma 17.12.2

Coherence is owned on arbitrary ringed sites by `SheafOfModules.IsCoherent`.  Its canonical
finite-presentation instance specializes directly to ringed spaces, and Mathlib then supplies
quasicoherence.
-/

@[expose] public section

open AlgebraicGeometry

universe u

variable {X : RingedSpace.{u}}
variable (ℱ : RingedSpace.Modules X) [ℱ.IsCoherent]

/- Lemma 17.12.2 (01BW): a coherent `O_X`-module is finitely presented. -/
@[stacks 01BW]
#check
  (SheafOfModules.IsCoherent.isFinitePresentation ℱ :
    ℱ.IsFinitePresentation)

/- A coherent `O_X`-module is consequently quasicoherent. -/
#check (inferInstance : ℱ.IsQuasicoherent)
