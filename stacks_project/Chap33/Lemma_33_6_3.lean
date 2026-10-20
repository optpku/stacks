/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced

@[expose] public section

universe u

/-!
# Lemma 33.6.3 compatibility entry point

The perfect-field reducedness criteria are owned by
`ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced`.
-/

/- Lemma 33.6.3: Over a perfect field, a reduced local ring gives geometric
reducedness at the corresponding point, and a reduced scheme is geometrically
reduced over the field. -/
@[stacks 020I] #check
  (AlgebraicGeometry.SchemeOverField.geometricallyReducedAt_of_isReduced_stalk_of_perfectField :
    ∀ {k : Type u} [Field k]
      (X : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k)))
      [PerfectField k] (x : X.left) [_root_.IsReduced (X.left.presheaf.stalk x)],
      AlgebraicGeometry.SchemeOverField.geometricallyReducedAt X x)

#check
  (AlgebraicGeometry.SchemeOverField.geometricallyReduced_of_isReduced_of_perfectField :
    ∀ {k : Type u} [Field k] [PerfectField k]
      (X : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k)))
      [AlgebraicGeometry.IsReduced X.left],
      AlgebraicGeometry.SchemeOverField.geometricallyReduced X)
