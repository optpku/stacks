/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.ProperSupport
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

/- 30.27.0.1: the completion functor
the completion functor from coherent `𝒪_X`-modules with support proper over `S` to coherent
formal `𝓘`-adic modules on `X` with support proper over `S`.
-/
@[stacks 088D] #check
  (AlgebraicGeometry.Scheme.Modules.coherentProperSupportCompletionFunctor :
    ∀ {X S : Scheme.{u}} {f : X ⟶ S} {I : X.IdealSheafData}
      [IsNoetherian X] [LocallyOfFiniteType f],
      AlgebraicGeometry.Scheme.Modules.CoherentProperSupportOver f ⥤
        AlgebraicGeometry.Scheme.Modules.CoherentFormalProperSupportOver f I)
