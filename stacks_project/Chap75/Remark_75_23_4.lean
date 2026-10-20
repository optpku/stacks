/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import stacks_project.Chap75.Remark_75_23_4_BaseChange

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory.DerivedCategory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open ComplexShape DerivedCategory.TStructure TopologicalSpace

universe u

/- Remark 75.23.4: the pseudo-coherent complex `L` of Lemma 75.23.3 (B) is
canonically associated to the situation. Formation of `L` is compatible with
base change: for a cartesian square of algebraic spaces, there are canonical
functorial isomorphisms
`Ext^i_{𝒪_{Y'}}(Lg^* L, F') ≅ Ext^i_{𝒪_{X'}}(L(g')^* E, (g')^* G ⊗ (f')^* F')`
for quasi-coherent `F'` on `Y'`. The complex `G` is pulled back termwise, not
by derived pullback. -/
@[stacks 0DKL] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.RepresentsExt.pullback :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
      [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived B)]
      [localizationMonoidal X]
      (f : X ⟶ B)
      [LocallyOfFiniteType f] [QuasiSeparated f] [IsNoetherian B]
      (H : MonoidalClosed (ModuleDerived X))
      (H_B : MonoidalClosed (ModuleDerived B))
      (E : ModuleDerived X)
      (hE_minus : (t.minus : ObjectProperty (ModuleDerived X)) E)
      (hE_coherent :
        DerivedCategory.cohomologyIn
          (SheafOfModules.isCoherent (structureSheaf X)) E)
      (G : CochainComplex (Modules X) ℤ)
      (hG_bounded : CochainComplex.bounded (Modules X) G)
      (hG_coherent : ∀ i : ℤ, (G.X i).IsCoherent)
      (hG_flat : ∀ i : ℤ, ∀ x, Modules.flatOverAt (G.X i) f x)
      (hG_support :
        ∀ i : ℤ,
          ClosedSubset.IsProperOver f
            (Closeds.closure (Modules.moduleSupport (G.X i))))
      (L : ModuleDerived B) (hL : IsPseudoCoherent B L)
      (hrep : RepresentsExt f H H_B E G L)
      {X' Y' : AlgebraicSpace S}
      [MonoidalCategory (ModuleDerived X')] [localizationMonoidal X']
      [MonoidalCategory (ModuleDerived Y')]
      (H' : MonoidalClosed (ModuleDerived X'))
      (H_Y' : MonoidalClosed (ModuleDerived Y'))
      (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ B)
      (sq : IsPullback g' f' f g),
      RepresentsExt f' H' H_Y' ((modulePullbackDerived g').obj E)
        (((Modules.pullback g').mapHomologicalComplex (up ℤ)).obj G)
        ((modulePullbackDerived g).obj L))
