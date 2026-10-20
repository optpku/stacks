/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.QuasiProjective.Composition

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 29.40.3: if the base scheme is quasi-compact and two scheme morphisms are
quasi-projective, then their composite is quasi-projective. -/
@[stacks 0C4M] #check
  (AlgebraicGeometry.QuasiProjective.comp :
    ∀ {X Y S : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S},
      [CompactSpace S] → QuasiProjective f → QuasiProjective g →
        QuasiProjective (f ≫ g))
