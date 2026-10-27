/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.FppfComplexDescent

/-!
# Lemma 85.35.2

A quasi-coherent complex with a coface cocycle descends along an fppf
hypercovering if its last-vertex pullbacks have vanishing negative self-Ext.
-/

@[expose] public section

universe u

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.Simplicial Opposite Functor
open scoped Simplicial

/- Lemma 85.35.2. Let `X` be an algebraic space over a scheme `S`. Let
`a : U ⟶ X` be an fppf hypercovering. Suppose given `K0 ∈ D_QCoh(U_0)` and an
isomorphism `α : L(f_{δ 1})^* K0 ⟶ L(f_{δ 0})^* K0` satisfying the cocycle
condition on `U_1`. Set `K_n = Lf_{τ^n_n}^* K0`. Assume
`Ext⁽i⁾(K_n, K_n) = 0` for `i < 0`. Then there exists an object
`K ∈ D_QCoh(O_X)` and an isomorphism `La_0^* K ≅ K0` compatible with `α`.
(The printed target `La_0^* K ⟶ K` is recovered as this stage-zero isomorphism
`La_0^* K ≅ K0`, as in the proof of tag 0DLA.) -/
@[stacks 0DLA] #check
  (AlgebraicGeometry.AlgebraicSpace.Simplicial.exists_derivedQCoh_of_cocycle :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      {U : SimplicialObject (AlgebraicSpace S)}
      (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X) (ha : IsFppfHypercovering a)
      (K0 : DerivedQCoh (U.obj (op ⦋0⦌)))
      (α : (modulePullbackDerived (U.δ (1 : Fin 2))).obj K0.obj ≅
        (modulePullbackDerived (U.δ (0 : Fin 2))).obj K0.obj)
      (hα : IsCocycle α) (h_ext : NegExtVanishing K0),
      ∃ (K : DerivedQCoh X)
        (e : (modulePullbackDerived (augmentationZero a)).obj K.obj ≅ K0.obj),
        CompatibleWith a K e α)
