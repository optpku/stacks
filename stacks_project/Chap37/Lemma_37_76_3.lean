/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Weighting.Semicontinuity

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.76.3: a positive integer-valued weighting of a locally quasi-finite morphism is
upper semicontinuous on the source. -/
@[stacks 0F3I] #check
  (AlgebraicGeometry.Scheme.Hom.IsWeighting.upperSemicontinuous :
    ∀ {X Y : Scheme.{u}} {f : X ⟶ Y} [LocallyOfFiniteType f] [LocallyQuasiFinite f]
      {w : X → ℤ}, f.IsWeighting w → (∀ x, 0 < w x) → UpperSemicontinuous w)

end AlgebraicGeometry.Scheme.Hom
