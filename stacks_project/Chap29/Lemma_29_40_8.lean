/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.QuasiProjective.Cancellation

open CategoryTheory

universe u

/- Lemma 29.40.8: Let `g : Y ⟶ S` and `f : X ⟶ Y` be morphisms of schemes. If
`f ≫ g` is quasi-projective and `f` is quasi-compact, then `f` is quasi-projective. -/
@[stacks 0C4N] #check
  (AlgebraicGeometry.QuasiProjective.of_comp :
    ∀ {X Y S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S}
      [AlgebraicGeometry.QuasiCompact f],
      AlgebraicGeometry.QuasiProjective (f ≫ g) → AlgebraicGeometry.QuasiProjective f)
