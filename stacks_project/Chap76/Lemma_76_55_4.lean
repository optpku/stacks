/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.AtWorstNodal.SourceLocus
import StacksCheckRecall

/-!
# Maximal open subspace where a morphism of algebraic spaces is at-worst-nodal

For a flat, locally finitely presented morphism of algebraic spaces, there is a
maximal open subspace of the source on which the restriction is at-worst-nodal
of relative dimension 1, and formation of this open commutes with arbitrary
base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace CategoryTheory.Limits

universe u

open AlgebraicGeometry.AlgebraicSpace.AtWorstNodal

/- Lemma 76.55.4 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` which is flat and locally of finite presentation.
Then there is a maximal open subspace `sourceLocus f ⊂ X` such that
`(sourceLocus f).ι ≫ f` is at-worst-nodal of relative dimension 1. -/
@[stacks 0DSH] #check
  (AlgebraicGeometry.AlgebraicSpace.AtWorstNodal.sourceLocus_isLargest :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f],
    AtWorstNodal ((sourceLocus f).ι ≫ f) ∧
      ∀ {U : AlgebraicSpace S} (i : U ⟶ X) [IsOpenImmersion i],
        AtWorstNodal (i ≫ f) →
          Set.range (Points.map i) ⊆ (sourceLocus f).pointsSet)

/- Lemma 76.55.4 (2): Formation of the maximal open subspace on which `f` is
at-worst-nodal of relative dimension 1 commutes with arbitrary cartesian base
change. -/
@[stacks 0DSH] #check
  (AlgebraicGeometry.AlgebraicSpace.AtWorstNodal.sourceLocus_eq_preimage_of_isPullback :
    ∀ {S : Scheme.{u}}
    {X Y X' Y' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
    (g : Y' ⟶ Y) (hcart : IsPullback g' f' f g) [Flat f]
    [LocallyOfFinitePresentation f],
    (sourceLocus f').pointsSet = Points.map g' ⁻¹' (sourceLocus f).pointsSet)

