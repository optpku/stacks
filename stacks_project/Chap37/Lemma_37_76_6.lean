/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Weighting.MaximumLocus
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.76.6: for a separated locally quasi-finite morphism with a positive
weighting whose fibre integral attains its maximum `d`, the restriction over the
open equality locus is finite. -/
@[stacks 0F3L] #check
  (AlgebraicGeometry.Scheme.Hom.IsWeighting.isFinite_restrict_maximumLocus :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ Y} [AlgebraicGeometry.IsSeparated f]
      [AlgebraicGeometry.LocallyOfFiniteType f] [AlgebraicGeometry.LocallyQuasiFinite f]
      [hf : Filter.TendstoCofinite (fun x : X ↦ f x)] {w : X → ℤ}
      (hw : f.IsWeighting w) (h_pos : ∀ x, 0 < w x) (d : ℤ)
      (h_max : IsGreatest (Set.range (f.fiberIntegral hf w)) d),
      AlgebraicGeometry.IsFinite
        (f ∣_ hw.fiberIntegralMaximumLocus h_pos d h_max))
