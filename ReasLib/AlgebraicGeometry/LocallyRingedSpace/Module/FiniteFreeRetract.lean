/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FiniteFreeRetract
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite-free retracts on locally ringed spaces

Local rings turn finite projective stalks into finite free modules.  Consequently, on a
locally ringed space the generic local finite-free-retract predicate agrees with finite local
freeness, and finite locally free module sheaves are closed under categorical retracts.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace SheafOfModules.RingedSite.FiniteFreeRetract

variable {X : LocallyRingedSpace.{u}}

/-- On a locally ringed space, a module sheaf which is locally a retract of finite free module
sheaves is finite locally free. -/
@[stacks 0BCI "local finite-free retract"]
theorem IsLocal.isFiniteLocallyFree
    (M : X.Modules) [IsLocal M] : M.IsFiniteLocallyFree := sorry

/-- On a locally ringed space, finite local freeness is equivalent to the generic ringed-site
property of being locally a retract of finite free module sheaves. -/
@[stacks 0BCI "local finite-free retract characterization"]
theorem isLocal_iff_isFiniteLocallyFree (M : X.Modules) :
    IsLocal M ↔ M.IsFiniteLocallyFree := sorry

end SheafOfModules.RingedSite.FiniteFreeRetract

namespace SheafOfModules.IsFiniteLocallyFree

variable {X : LocallyRingedSpace.{u}}

/-- Lemma 17.14.6 (0BCI): a categorical retract of a finite locally free module sheaf on a
locally ringed space is finite locally free. -/
@[stacks 0BCI]
theorem ofRetract {M N : X.Modules} [N.IsFiniteLocallyFree]
    (r : Retract M N) : M.IsFiniteLocallyFree := sorry

end SheafOfModules.IsFiniteLocallyFree
