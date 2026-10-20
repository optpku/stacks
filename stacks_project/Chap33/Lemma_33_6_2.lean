/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 33.6.2: a scheme over a field is geometrically reduced at a point if and only if
its local ring at that point is geometrically reduced over the field. -/
@[stacks 035W] #check
  (AlgebraicGeometry.SchemeOverField.geometricallyReducedAt_iff_isGeometricallyReduced :
    ∀ {k : Type u} [Field k]
      (X : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k))) (x : X.left),
      AlgebraicGeometry.SchemeOverField.geometricallyReducedAt X x ↔
        Algebra.IsGeometricallyReduced k (X.left.presheaf.stalk x))
