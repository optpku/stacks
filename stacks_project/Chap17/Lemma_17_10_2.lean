/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent.Biproduct
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
import StacksCheckRecall

/-!
# Binary direct sums of quasicoherent modules

The site-theoretic closure theorem lives in ReasLib.  This file records its specialization to
modules on a ringed space.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Lemma 17.10.2 (01BF): the direct sum of two quasicoherent `O_X`-modules is quasicoherent. -/
@[stacks 01BF]
#check fun {X : RingedSpace.{u}} (M N : X.Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] ↦
  SheafOfModules.IsQuasicoherent.biprod (M := M) (N := N)

end AlgebraicGeometry
