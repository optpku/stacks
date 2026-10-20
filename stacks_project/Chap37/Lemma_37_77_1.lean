/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Weighting.AffineMaximumLocus
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.77.1: for a quasi-finite finitely presented morphism between affine schemes,
the open where the fibre integral of a positive weighting attains its maximum is affine. -/
@[stacks 0F3R]
#check
  (AlgebraicGeometry.Scheme.Hom.IsWeighting.isAffineOpen_fiberIntegralMaximumLocus :
    ∀ {X Y : Scheme.{u}} {f : X ⟶ Y} [IsAffine X] [IsAffine Y]
        [QuasiFinite f] [FinitePresentation f] {w : X → ℤ} (hw : f.IsWeighting w)
        (h_pos : ∀ x : X, 0 < w x) (d : ℤ)
        (h_max : IsGreatest
          (Set.range (f.fiberIntegral (tendstoCofinite_of_compactSource f) w)) d),
      IsAffineOpen (hw.fiberIntegralMaximumLocus h_pos d h_max))

end AlgebraicGeometry.Scheme.Hom
