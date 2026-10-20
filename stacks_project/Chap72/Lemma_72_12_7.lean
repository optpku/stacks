/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldExtension.Galois.Closeds.Descent

/-!
# Galois descent of closed subsets of algebraic spaces

A Galois-invariant closed subset of `|X_K|` is the inverse image of a closed
subset of `|X|` along `|X_K| → |X|`.
-/

@[expose] public section

universe u

/- Lemma 72.12.7: Let `k` be a field. Let `K / k` be a (possibly infinite) Galois
extension. Let `X` be an algebraic space over `k`. Let `Tbar ⊂ |X_K|` be a closed
subset such that `σ(Tbar) = Tbar` for every `σ : Gal(K/k)`. Then there exists a
closed subset `T ⊂ |X|` whose inverse image along `|X_K| → |X|` is `Tbar`. -/
@[stacks 0A16] #check
  (AlgebraicGeometry.AlgebraicSpace.FieldExtension.Galois.Closeds.exists_preimage_eq_of_image :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
      (X : AlgebraicGeometry.AlgebraicSpace (AlgebraicGeometry.Spec (CommRingCat.of k)))
      (Tbar : TopologicalSpace.Closeds (AlgebraicGeometry.AlgebraicSpace.Points
        (AlgebraicGeometry.AlgebraicSpace.FieldExtension.baseChange k K X))),
      (∀ σ : Gal(K/k),
        AlgebraicGeometry.AlgebraicSpace.Points.map
            (AlgebraicGeometry.AlgebraicSpace.FieldExtension.Galois.map k K X σ) ''
          (Tbar : Set _) = (Tbar : Set _)) →
      ∃ T : TopologicalSpace.Closeds (AlgebraicGeometry.AlgebraicSpace.Points X),
        AlgebraicGeometry.AlgebraicSpace.FieldExtension.Galois.Closeds.preimage k K T = Tbar)
