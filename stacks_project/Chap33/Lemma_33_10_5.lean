/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Normal.Product

@[expose] public section

universe u

/-
Lemma 33.10.5: let `k` be a field. Let `X` be a geometrically normal scheme over `k` and let
`Y` be a normal scheme over `k`. Then `X ×[Spec (CommRingCat.of k)] Y` is a normal scheme.
-/
@[stacks 06DG] #check
  (AlgebraicGeometry.SchemeOverField.isNormal_pullback_of_geometricallyNormal_left :
    ∀ {k : Type u} [Field k]
      (X Y : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k))),
      AlgebraicGeometry.SchemeOverField.geometricallyNormal X →
        AlgebraicGeometry.Scheme.isNormal Y.left →
          AlgebraicGeometry.Scheme.isNormal
            (CategoryTheory.Limits.pullback X.hom Y.hom : AlgebraicGeometry.Scheme))
