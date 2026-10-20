/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree.Birational
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 33.44.4 (1): pullback along a birational morphism between proper schemes of dimension at
most one over a field preserves the degree of every finite locally free module of constant rank. -/
@[stacks 0AYU] #check
  (AlgebraicGeometry.Scheme.Modules.curveDegree_pullback_eq_of_isBirational :
    ∀ {k : Type u} [Field k] {X X' : AlgebraicGeometry.Scheme.{u}}
      (g : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) [AlgebraicGeometry.IsProper g]
      (g' : X' ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) [AlgebraicGeometry.IsProper g']
      (f : X' ⟶ X) [AlgebraicGeometry.IsBirational f] (hfk : f ≫ g = g')
      (hXdim : topologicalKrullDim X ≤ 1) (hX'dim : topologicalKrullDim X' ≤ 1)
      (ℰ : X.Modules) (n : ℕ)
      [AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeOfRank n ℰ],
      AlgebraicGeometry.Scheme.Modules.curveDegree g' hX'dim
          ((AlgebraicGeometry.Scheme.Modules.pullback f).obj ℰ) n =
        AlgebraicGeometry.Scheme.Modules.curveDegree g hXdim ℰ n)

/- Lemma 33.44.4 (2): more generally, it suffices that the morphism biject the generic points of
the one-dimensional irreducible components and induce stalk isomorphisms at those source points. -/
@[stacks 0AYU] #check
  (AlgebraicGeometry.Scheme.Modules.curveDegree_pullback_eq_of_bijOn_oneDimensionalGenericPoints :
    ∀ {k : Type u} [Field k] {X X' : AlgebraicGeometry.Scheme.{u}}
      (g : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) [AlgebraicGeometry.IsProper g]
      (g' : X' ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) [AlgebraicGeometry.IsProper g']
      (f : X' ⟶ X) (hfk : f ≫ g = g')
      (hXdim : topologicalKrullDim X ≤ 1) (hX'dim : topologicalKrullDim X' ≤ 1)
      (hgeneric : Set.BijOn f.base
        (AlgebraicGeometry.Scheme.oneDimensionalGenericPoints X')
        (AlgebraicGeometry.Scheme.oneDimensionalGenericPoints X))
      (hstalk : ∀ {η : X'},
        η ∈ AlgebraicGeometry.Scheme.oneDimensionalGenericPoints X' →
          CategoryTheory.IsIso (f.stalkMap η))
      (ℰ : X.Modules) (n : ℕ)
      [AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeOfRank n ℰ],
      AlgebraicGeometry.Scheme.Modules.curveDegree g' hX'dim
          ((AlgebraicGeometry.Scheme.Modules.pullback f).obj ℰ) n =
        AlgebraicGeometry.Scheme.Modules.curveDegree g hXdim ℰ n)
