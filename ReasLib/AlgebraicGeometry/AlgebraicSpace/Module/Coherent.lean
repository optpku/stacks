/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Sheafification
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Zero

/-!
# Coherent modules on the small étale site

Coherence is the intrinsic ringed-site property `SheafOfModules.IsCoherent`.
-/

@[expose] public section

open CategoryTheory
open scoped ZeroObject

universe u

namespace AlgebraicGeometry.AlgebraicSpace.SmallEtale.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The zero module on an algebraic space is coherent. -/
instance isCoherentZero :
    SheafOfModules.IsCoherent (R := structureSheaf X) (0 : Modules X) := sorry

end AlgebraicGeometry.AlgebraicSpace.SmallEtale.Modules
