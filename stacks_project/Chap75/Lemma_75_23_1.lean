/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap75.Lemma_75_23_1_Comparison
import StacksCheckRecall

/-!
# Lemma 75.23.1

Functorial isomorphisms comparing `H^i(B, K ⊗ᴸ F)` with
`H^i(X, E ⊗ᴸ (G ⊗ f^* F))`, compatible with connecting maps of a short exact
sequence of quasi-coherent modules on `B`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory.DerivedCategory ComplexShape TopologicalSpace

universe u

/- Lemma 75.23.1 (1): assumptions and notation as in Lemma 75.22.2. Then there
are functorial isomorphisms
`H^i(B, K ⊗ᴸ F) ⟶ H^i(X, E ⊗ᴸ (G ⊗ f^* F))`
for `F` quasi-coherent on `B`. The binder `hG_flat` is the Comparison-side
spelling of Lemma 75.22.2 flatness, the same étale-chart criterion, because
Chap67.flatOver is not importable beside cohomologyAb. -/
@[stacks 0A1M] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.cohomologyComparison_isIso :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
      [LocallyOfFiniteType f] [QuasiSeparated f] [IsNoetherian B]
      (E : ModuleDerived X) (hE : IsPerfect E)
      (G : CochainComplex (Modules X) ℤ)
      (hG_bounded : CochainComplex.bounded (Modules X) G)
      (hG_coherent : ∀ i : ℤ, (G.X i).IsCoherent)
      (hG_flat : ∀ i : ℤ, ∀ x, Modules.flatOverAt (G.X i) f x)
      (hG_support : ∀ i : ℤ,
        ClosedSubset.IsProperOver f (Closeds.closure (Modules.moduleSupport (G.X i))))
      (F : Modules B) (hF : quasiCoherentModuleProperty B F) (i : ℤ),
      IsIso (cohomologyComparison f E G F i))

/- Lemma 75.23.1 (2): the isomorphisms of Lemma 75.23.1 (1) are compatible with
boundary maps of a short exact sequence of quasi-coherent modules on `B`.
The binder `hG_flat` is the Comparison-side spelling of Lemma 75.22.2
flatness, the same étale-chart criterion, because Chap67.flatOver is not
importable beside cohomologyAb. -/
@[stacks 0A1M] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.cohomologyComparison_boundary :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
      [LocallyOfFiniteType f] [QuasiSeparated f] [IsNoetherian B]
      (E : ModuleDerived X) (hE : IsPerfect E)
      (G : CochainComplex (Modules X) ℤ)
      (hG_bounded : CochainComplex.bounded (Modules X) G)
      (hG_coherent : ∀ i : ℤ, (G.X i).IsCoherent)
      (hG_flat : ∀ i : ℤ, ∀ x, Modules.flatOverAt (G.X i) f x)
      (hG_support : ∀ i : ℤ,
        ClosedSubset.IsProperOver f (Closeds.closure (Modules.moduleSupport (G.X i))))
      (s : ShortComplex (Modules B)) (hs : s.ShortExact)
      (hs0 : (s.map (HomologicalComplex.single (Modules B) (up ℤ) 0)).ShortExact)
      (hF₁ : quasiCoherentModuleProperty B s.X₁)
      (hF₂ : quasiCoherentModuleProperty B s.X₂)
      (hF₃ : quasiCoherentModuleProperty B s.X₃) (i : ℤ),
      cohomologyComparison f E G s.X₃ i ≫
          cohomologyTargetδ f E G s
            (complexTensorPullback_shortExact f G hG_flat s hs) i =
        cohomologySourceδ f E G s hs0 i ≫
          cohomologyComparison f E G s.X₁ (i + 1))
