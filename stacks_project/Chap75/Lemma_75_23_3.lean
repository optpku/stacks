/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.ProjectionFormula.ExtRepresentability
import StacksCheckRecall

/-!
# Lemma 75.23.3

Functorial maps comparing `Ext^i_{𝒪_X}(E, G ⊗ f^* F)` with hypercohomology of
a perfect approximation on `B`, and functorial isomorphisms representing those
Ext groups by a pseudo-coherent object of `D(𝒪_B)`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory.DerivedCategory CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed ComplexShape DerivedCategory.TStructure
open TopologicalSpace
open scoped CategoryTheory.DerivedCategory.DerivedTensor

universe u

/- Lemma 75.23.3 (1): for every `m`, there is a perfect object `K` of `D(𝒪_B)`
and functorial maps
`Ext^i_{𝒪_X}(E, G ⊗ f^* F) ⟶ H^i(B, K ⊗ᴸ F)`
for `F` quasi-coherent on `B`, compatible with connecting maps, and
isomorphisms for `i ≤ m`. -/
@[stacks 08JR] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.existsPerfectExtApproximation :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
      [MonoidalCategory (ModuleDerived X)] [localizationMonoidal X]
      (f : X ⟶ B)
      [LocallyOfFiniteType f] [QuasiSeparated f] [IsNoetherian B]
      (H : MonoidalClosed (ModuleDerived X))
      (E : ModuleDerived X)
      (hE_minus : (t.minus : ObjectProperty (ModuleDerived X)) E)
      (hE_coherent :
        DerivedCategory.cohomologyIn
          (SheafOfModules.isCoherent (structureSheaf X)) E)
      (G : CochainComplex (Modules X) ℤ)
      (hG_bounded : CochainComplex.bounded (Modules X) G)
      (hG_coherent : ∀ i : ℤ, (G.X i).IsCoherent)
      (hG_flat : ∀ i : ℤ, ∀ x, Modules.flatOverAt (G.X i) f x)
      (hG_support : ∀ i : ℤ,
        ClosedSubset.ProperOver f
          (Closeds.closure (Modules.moduleSupport (G.X i))))
      (m : ℤ),
      ∃ (K : ModuleDerived B)
        (α :
          ∀ (F : Modules B) (_ : quasiCoherentModuleProperty B F) (i : ℤ),
            cohomologyAb X (extTarget f H E G F) i ⟶
              cohomologyAb B
                (DerivedTensor.Right.obj K
                  ((DerivedCategory.singleFunctor (Modules B) 0).obj F)) i),
        IsPerfectExtApproximation f H E G m K α)

/- Lemma 75.23.3 (2): there is a pseudo-coherent object `L` of `D(𝒪_B)` and
functorial isomorphisms
`Ext^i_{𝒪_B}(L, F) ⟶ Ext^i_{𝒪_X}(E, G ⊗ f^* F)`
for `F` quasi-coherent on `B`, compatible with connecting maps. -/
@[stacks 08JR] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.existsPseudoCoherentExtRepresentation :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
      [MonoidalCategory (ModuleDerived X)] [localizationMonoidal X]
      (f : X ⟶ B)
      [LocallyOfFiniteType f] [QuasiSeparated f] [IsNoetherian B]
      [MonoidalCategory (ModuleDerived B)] [localizationMonoidal B]
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
      (hG_support : ∀ i : ℤ,
        ClosedSubset.ProperOver f
          (Closeds.closure (Modules.moduleSupport (G.X i)))),
      ∃ (L : ModuleDerived B)
        (α :
          ∀ (F : Modules B) (_ : quasiCoherentModuleProperty B F) (i : ℤ),
            cohomologyAb B
                ((ihomOf H_B L).obj
                  ((DerivedCategory.singleFunctor (Modules B) 0).obj F)) i ⟶
              cohomologyAb X (extTarget f H E G F) i),
        IsPseudoCoherentExtRepresentation f H H_B E G L α)
