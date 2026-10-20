/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Variety.GeometricallyIntegral

@[expose] public section

open CategoryTheory

universe u

/- Lemma 33.25.10: let `k` be a field and let `X` be a variety over `k`. If `x` is a
`k`-rational point of `X` and `X` is smooth at `x`, then `X` is geometrically integral over `k`.
-/
@[stacks 0CDW] #check
  (AlgebraicGeometry.geometricallyIntegral_of_smoothAt_of_rationalPoint :
    ∀ {k : Type u} [Field k]
      (X : Over (AlgebraicGeometry.Spec (CommRingCat.of k))) [AlgebraicGeometry.Variety X]
      (x : X.left) [IsIso (X.hom.residueFieldMap x)] (h_smooth : X.hom.SmoothAt x),
      AlgebraicGeometry.GeometricallyIntegral X.hom)
