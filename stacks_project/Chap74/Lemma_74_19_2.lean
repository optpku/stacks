/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyQuasiFinite.LocalAtSource
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.19.2: the property `P(f)` given by “`f` is locally quasi-finite” is
étale local on the source. -/
@[stacks 06F5] #check
  (AlgebraicGeometry.AlgebraicSpace.FiniteType.locallyQuasiFiniteIsLocalAtSourceEtale :
    MorphismProperty.IsLocalAtSource
      (@LocallyOfFiniteType S ⊓ @LocallyQuasiFinite S :
        MorphismProperty (AlgebraicSpace S))
      (@etalePrecoverage S))
