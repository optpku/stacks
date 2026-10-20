/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap75.Lemma_75_23_2_Comparison
import StacksCheckRecall

/-!
# Lemma 75.23.2

Functorial isomorphisms comparing `H^i(B, K ⊗ᴸ F)` with
`Ext^i_{𝒪_X}(E, G ⊗ f^* F)`, compatible with connecting maps of a short exact
sequence of quasi-coherent modules on `B`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory.DerivedCategory CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed ComplexShape TopologicalSpace

universe u

/- Lemma 75.23.2 (1): assumptions and notation as in Lemma 75.22.3. Then there
are functorial isomorphisms
`H^i(B, K ⊗ᴸ F) ⟶ Ext^i_{𝒪_X}(E, G ⊗ f^* F)`
for `F` quasi-coherent on `B`. The binder `hG_flat` is the Comparison-side
spelling of Lemma 75.22.3 flatness, the same étale-chart criterion, because
Chap67.flatOver is not importable beside cohomologyAb. -/
@[stacks 08JN] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.extComparison_isIso :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
      [MonoidalCategory (ModuleDerived X)] [localizationMonoidal X]
      (f : X ⟶ B)
      [LocallyOfFiniteType f] [QuasiSeparated f] [IsNoetherian B]
      (H : MonoidalClosed (ModuleDerived X))
      (E : ModuleDerived X) (hE : IsPerfect E)
      (G : CochainComplex (Modules X) ℤ)
      (hG_bounded : CochainComplex.bounded (Modules X) G)
      (hG_coherent : ∀ i : ℤ, (G.X i).IsCoherent)
      (hG_flat : ∀ i : ℤ, ∀ x, Modules.flatOverAt (G.X i) f x)
      (hG_support : ∀ i : ℤ,
        ClosedSubset.IsProperOver f (Closeds.closure (Modules.moduleSupport (G.X i))))
      (F : Modules B) (hF : quasiCoherentModuleProperty B F) (i : ℤ),
      IsIso (extComparison f H E G F i))

/- Lemma 75.23.2 (2): the isomorphisms of Lemma 75.23.2 (1) are compatible with
boundary maps of a short exact sequence of quasi-coherent modules on `B`.
The binder `hG_flat` is the Comparison-side spelling of Lemma 75.22.3
flatness, the same étale-chart criterion, because Chap67.flatOver is not
importable beside cohomologyAb. -/
@[stacks 08JN] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.extComparison_boundary :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
      [MonoidalCategory (ModuleDerived X)] [localizationMonoidal X]
      (f : X ⟶ B)
      [LocallyOfFiniteType f] [QuasiSeparated f] [IsNoetherian B]
      (H : MonoidalClosed (ModuleDerived X))
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
      (hF₃ : quasiCoherentModuleProperty B s.X₃) (i : ℤ)
      [(tensorLeft E).CommShift ℤ],
      extComparison f H E G s.X₃ i ≫
          extTargetδ f H E G s
            (complexTensorPullback_shortExact f G hG_flat s hs) i =
        extSourceδ f H E G s hs0 i ≫
          extComparison f H E G s.X₁ (i + 1))
