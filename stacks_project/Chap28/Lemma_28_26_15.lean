/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.ExternalTensor
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 28.26.15: over a quasi-separated scheme, the external tensor product of ample
invertible modules is ample on the fiber product. -/
@[stacks 0DNK] #check
  (AlgebraicGeometry.Scheme.Modules.isAmple_externalTensorProduct :
    ∀ {S X Y : Scheme.{u}} [QuasiSeparatedSpace S]
      (f : X ⟶ S) (g : Y ⟶ S) (L : X.Modules) (N : Y.Modules)
      [Invertible L] [Invertible N] [IsAmple L] [IsAmple N],
      IsAmple (externalTensorProduct f g L N))

end AlgebraicGeometry.Scheme.Modules
