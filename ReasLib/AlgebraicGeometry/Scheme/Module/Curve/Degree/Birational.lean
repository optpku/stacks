/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.Dimension
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.GenericPoints

/-!
# Curve Degree under Birational Pullback

This module records invariance of the degree of a finite locally free module under pullback along
morphisms that agree generically on the one-dimensional irreducible components.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

section

variable {k : Type u} [Field k] {X X' : Scheme.{u}}

/-- Pullback preserves curve degree when a morphism between proper schemes of dimension at most
one bijects the generic points of their one-dimensional irreducible components and induces
isomorphisms on the corresponding stalks. -/
theorem curveDegree_pullback_eq_of_bijOn_oneDimensionalGenericPoints
    (g : X ⟶ Spec (CommRingCat.of k)) [IsProper g]
    (g' : X' ⟶ Spec (CommRingCat.of k)) [IsProper g']
    (f : X' ⟶ X) (hfk : f ≫ g = g')
    (hXdim : topologicalKrullDim X ≤ 1) (hX'dim : topologicalKrullDim X' ≤ 1)
    (hgeneric : Set.BijOn f.base
      (Scheme.oneDimensionalGenericPoints X') (Scheme.oneDimensionalGenericPoints X))
    (hstalk : ∀ {η : X'}, η ∈ Scheme.oneDimensionalGenericPoints X' → IsIso (f.stalkMap η))
    (ℰ : X.Modules) (n : ℕ) [IsFiniteLocallyFreeOfRank n ℰ] :
    curveDegree g' hX'dim ((Scheme.Modules.pullback f).obj ℰ) n =
      curveDegree g hXdim ℰ n := sorry

/-- Pullback along a birational morphism between proper schemes of dimension at most one
preserves the curve degree of every finite locally free module of constant rank. -/
theorem curveDegree_pullback_eq_of_isBirational
    (g : X ⟶ Spec (CommRingCat.of k)) [IsProper g]
    (g' : X' ⟶ Spec (CommRingCat.of k)) [IsProper g']
    (f : X' ⟶ X) [IsBirational f] (hfk : f ≫ g = g')
    (hXdim : topologicalKrullDim X ≤ 1) (hX'dim : topologicalKrullDim X' ≤ 1)
    (ℰ : X.Modules) (n : ℕ) [IsFiniteLocallyFreeOfRank n ℰ] :
    curveDegree g' hX'dim ((Scheme.Modules.pullback f).obj ℰ) n =
      curveDegree g hXdim ℰ n := sorry

end

end AlgebraicGeometry.Scheme.Modules
