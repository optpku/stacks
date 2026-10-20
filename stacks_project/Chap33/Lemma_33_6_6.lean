/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced.BaseChange

@[expose] public section

open CategoryTheory

universe u

/- Lemma 33.6.6 (1): Let `k'/k` be a field extension, let `X` be a scheme over
`k`, let `x ∈ X`, and let `x' ∈ X_{k'}` lie over `x`. Then `X` is
geometrically reduced at `x` if and only if `X_{k'}` is geometrically reduced
at `x'`. -/
@[stacks 0384]
#check (AlgebraicGeometry.SchemeOverField.geometricallyReducedAt.iff_baseChange :
  ∀ {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    (X : Over (AlgebraicGeometry.Spec (CommRingCat.of k)))
    (x : X.left) (x' : (AlgebraicGeometry.FieldExtension.Over.baseChange k k' X).left),
    AlgebraicGeometry.FieldExtension.Over.toSource k k' X x' = x →
      (AlgebraicGeometry.SchemeOverField.geometricallyReducedAt X x ↔
        AlgebraicGeometry.SchemeOverField.geometricallyReducedAt
          (AlgebraicGeometry.FieldExtension.Over.baseChange k k' X) x'))

/- In particular, geometric reducedness of a scheme over a field is invariant
under extension of the ground field. -/
#check (AlgebraicGeometry.SchemeOverField.geometricallyReduced.iff_baseChange :
  ∀ {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    (X : Over (AlgebraicGeometry.Spec (CommRingCat.of k))),
    AlgebraicGeometry.SchemeOverField.geometricallyReduced X ↔
      AlgebraicGeometry.SchemeOverField.geometricallyReduced
        (AlgebraicGeometry.FieldExtension.Over.baseChange k k' X))
