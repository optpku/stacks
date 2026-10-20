/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.QuasiProjective
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 29.40.5: An H-quasi-projective morphism is quasi-projective. -/
@[stacks 01VY] #check
  (AlgebraicGeometry.HQuasiProjective.toQuasiProjective :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S},
      AlgebraicGeometry.HQuasiProjective f → AlgebraicGeometry.QuasiProjective f)
