/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Geometrically.Reduced.Etale
import StacksCheckRecall

/-!
# Étale-local invariance of geometric reducedness

Geometric reducedness of algebraic spaces over a field is étale-local: it is
detected at a point after a morphism étale at that point, and globally after a
surjective étale morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace CommRingCat

noncomputable section

universe u

/- Lemma 72.11.7 (1): Let `k` be a field. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `k`. Let `x` be a point of `|X|` with image `y` in `|Y|`.
If `f` is étale at `x`, then `X` is geometrically reduced at `x` if and only if
`Y` is geometrically reduced at `y`. -/
@[stacks 0E05] #check
  (AlgebraicGeometry.AlgebraicSpace.geometricallyReducedAt_iff_of_etaleAt :
    ∀ {k : Type u} [Field k]
      {X Y : AlgebraicSpace (Spec (of k))} (f : X ⟶ Y) {x : Points X}
      (hf : EtaleAt f x),
      GeometricallyReducedAt X x ↔ GeometricallyReducedAt Y (Points.map f x))

/- Lemma 72.11.7 (2): Let `k` be a field. Let `f : X ⟶ Y` be a surjective étale
morphism of algebraic spaces over `k`. Then `X` is geometrically reduced if and
only if `Y` is geometrically reduced. -/
@[stacks 0E05] #check
  (AlgebraicGeometry.AlgebraicSpace.geometricallyReduced_iff_of_surjective_etale :
    ∀ {k : Type u} [Field k]
      {X Y : AlgebraicSpace (Spec (of k))} (f : X ⟶ Y) [Etale f] [Surjective f],
      GeometricallyReduced X ↔ GeometricallyReduced Y)
