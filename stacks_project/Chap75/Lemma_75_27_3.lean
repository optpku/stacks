/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.FlatPullbackSections

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FlatPullbackSections

open AlgebraicGeometry.AlgebraicSpace CategoryTheory.HomotopyColimit
open CategoryTheory.MonoidalClosed

/- Lemma 75.27.3 (1): for a flat morphism `f : U ⟶ X` of algebraic spaces of finite
presentation over a ring `A`, there is an inverse system `L : ℕᵒᵖ ⥤ D(𝒪_X)` of
perfect objects such that `K ↦ RΓ(U, Lf^* K)` is functorially its sequential
`RHom` homotopy-colimit presentation in `D(A)`. -/
@[stacks 0CRW] #check
  (AlgebraicGeometry.AlgebraicSpace.FlatPullbackSections.exists_perfect_rHom :
    ∀ {A : Type u} [CommRing A]
      {X U : AlgebraicSpace (Spec (CommRingCat.of A))} (f : U ⟶ X)
      [FinitePresentation (SchemeRealization.toBase X)] [FinitePresentation (SchemeRealization.toBase U)] [Flat f]
      [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
      (H : MonoidalClosed (ModuleDerived X))
      (T : CategoryTheory.DerivedCategory.DerivedTensor.Right.Monoidal.Model (C := Modules X)),
      ∃ L : ℕᵒᵖ ⥤ ModuleDerived X,
        (∀ n : ℕ, ModuleDerived.IsPerfect (L.obj (Opposite.op n))) ∧
          Functorial.IsOf (rHomDiagram H L) (pullbackFunctor f))

/- Lemma 75.27.3 (2): for a flat morphism `f : U ⟶ X` of algebraic spaces of finite
presentation over a ring `A`, there is a direct system `E : ℕ ⥤ D(𝒪_X)` of perfect
objects such that `K ↦ RΓ(U, Lf^* K)` is functorially the sequential homotopy
colimit of `K ↦ RΓ(X, Eₙ ⊗ᴸ K)` in `D(A)`. -/
@[stacks 0CRW] #check
  (AlgebraicGeometry.AlgebraicSpace.FlatPullbackSections.exists_perfect_tensor :
    ∀ {A : Type u} [CommRing A]
      {X U : AlgebraicSpace (Spec (CommRingCat.of A))} (f : U ⟶ X)
      [FinitePresentation (SchemeRealization.toBase X)] [FinitePresentation (SchemeRealization.toBase U)] [Flat f],
      ∃ E : ℕ ⥤ ModuleDerived X,
        (∀ n : ℕ, ModuleDerived.IsPerfect (E.obj n)) ∧
          Functorial.IsOf (tensorDiagram E) (pullbackFunctor f))

end AlgebraicGeometry.AlgebraicSpace.FlatPullbackSections
