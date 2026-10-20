/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Weighting.Semicontinuity
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.76.4: the fibre integral of a positive integer-valued weighting of a
separated locally quasi-finite morphism with finite fibres is lower semicontinuous. -/
@[stacks 0F3J] #check
  (AlgebraicGeometry.Scheme.Hom.IsWeighting.lowerSemicontinuous_fiberIntegral :
    ∀ {X Y : Scheme.{u}} {f : X ⟶ Y} [IsSeparated f]
      [LocallyOfFiniteType f] [LocallyQuasiFinite f]
      [hf : Filter.TendstoCofinite (fun x : X ↦ f x)] {w : X → ℤ},
      f.IsWeighting w → (∀ x, 0 < w x) → LowerSemicontinuous (f.fiberIntegral hf w))

end AlgebraicGeometry.Scheme.Hom
