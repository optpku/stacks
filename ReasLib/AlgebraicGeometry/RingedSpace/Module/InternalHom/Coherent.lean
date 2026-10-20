/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom.Coherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent
import Mathlib.Tactic.CrossRefAttribute

/-!
# Coherence of internal Hom on a ringed space

The public statements retain only the closed source object used to write internal Hom; the
canonical restriction-comparison mechanism belongs to the generic ringed-site owner and is not
exposed here.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalClosed
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.InternalHom

variable {X : RingedSpace.{u}}

/-- Internal Hom from a finitely presented module on a ringed space admits a local finite-kernel
presentation by copies of the target. -/
@[stacks 01CQ "local kernel on a ringed space"]
theorem finiteKernelIsLocal (F G : X.Modules)
    [F.IsFinitePresentation] :
    SheafOfModules.RingedSite.FiniteKernel.IsLocal G ((ihom F).obj G) := sorry

/-- Internal Hom from a finitely presented module to a coherent module on a ringed space is
coherent. -/
@[stacks 01CQ "coherence on a ringed space"]
theorem isCoherent (F G : X.Modules)
    [F.IsFinitePresentation] [G.IsCoherent] :
    ((ihom F).obj G).IsCoherent := sorry

end AlgebraicGeometry.RingedSpace.InternalHom
