/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.DerivedCocycle
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.FppfHypercovering

/-!
# Fppf descent of quasi-coherent complexes

Quasi-coherent derived objects with a coface cocycle descend along an fppf
hypercovering when their last-vertex pullbacks have no negative self-extensions.
-/

@[expose] public section

universe u

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open Opposite Functor
open scoped Simplicial

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}}

/-- A quasi-coherent derived object with a coface cocycle on an fppf hypercovering
and vanishing negative self-Ext at every last-vertex pullback descends to a
quasi-coherent derived object with a compatible degree-zero isomorphism. -/
@[stacks 0DLA]
theorem exists_derivedQCoh_of_cocycle {X : AlgebraicSpace S}
    {U : SimplicialObject (AlgebraicSpace S)}
    (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X) (ha : IsFppfHypercovering a)
    (K0 : DerivedQCoh (U.obj (op ⦋0⦌)))
    (α : (modulePullbackDerived (U.δ (1 : Fin 2))).obj K0.obj ≅
      (modulePullbackDerived (U.δ (0 : Fin 2))).obj K0.obj)
    (hα : IsCocycle α) (h_ext : NegExtVanishing K0) :
    ∃ (K : DerivedQCoh X)
      (e : (modulePullbackDerived (augmentationZero a)).obj K.obj ≅ K0.obj),
      CompatibleWith a K e α :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
