/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiFinite.Locus

/-!
# Quasi-finite part of a locally finite-type morphism of algebraic spaces

A locally finite-type morphism of algebraic spaces has a canonical open
subspace of the source on which it is locally quasi-finite, the relative
dimension is at least `1` off that open, and formation of the open commutes
with arbitrary base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.34.7 (1): The canonical open subspace of a locally finite-type
morphism is locally quasi-finite over the target, and the relative dimension
at each point outside this open is at least one. -/
@[stacks 04NW] #check (AlgebraicGeometry.AlgebraicSpace.locallyQuasiFinite_quasiFiniteLocus :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f],
    LocallyQuasiFinite ((quasiFiniteLocus f).ι ≫ f) ∧
      ∀ x : Points X, x ∉ Set.range (Points.map (quasiFiniteLocus f).ι) →
        (1 : WithBot ℕ∞) ≤ fiberDimensionAt f x)

/- Lemma 67.34.7 (2): Formation of the canonical quasi-finite open subspace
commutes with arbitrary base change. -/
@[stacks 04NW] #check
  (AlgebraicGeometry.AlgebraicSpace.quasiFiniteLocus_pointsSet_eq_preimage_of_isPullback :
    ∀ {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
      (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
      (hpb : IsPullback g' f' f g) [LocallyOfFiniteType f] [LocallyOfFiniteType f'],
      Set.range (Points.map (quasiFiniteLocus f').ι) =
        Points.map g' ⁻¹' Set.range (Points.map (quasiFiniteLocus f).ι))

end AlgebraicGeometry.AlgebraicSpace
