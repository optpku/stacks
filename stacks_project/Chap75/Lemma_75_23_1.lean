/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.ProjectionFormula.Cohomology
import StacksCheckRecall

/-! # Functorial cohomology isomorphisms compatible with connecting maps -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory.DerivedCategory ComplexShape TopologicalSpace

universe u

/- Lemma 75.23.1: for a perfect derived module and a bounded coherent relatively flat
complex with proper support, the canonical tensor cohomology comparison is an isomorphism. -/
@[stacks 0A1M] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.cohomologyComparison_isIso :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
      [LocallyOfFiniteType f] [QuasiSeparated f] [IsNoetherian B]
      (E : ModuleDerived X) (hE : IsPerfect E)
      (G : CochainComplex (Modules X) ℤ)
      (hG_bounded : CochainComplex.bounded (Modules X) G)
      (hG_coherent : ∀ i : ℤ, (G.X i).IsCoherent)
      (hG_flat : ∀ i : ℤ, Modules.flatOver (G.X i) f)
      (hG_support : ∀ i : ℤ,
        ClosedSubset.ProperOver f (Closeds.closure (Modules.moduleSupport (G.X i))))
      (F : Modules B) (hF : quasiCoherentModuleProperty B F) (i : ℤ),
      IsIso (cohomologyComparison f E G F i))

/- Lemma 75.23.1: the comparison is functorial in the quasi-coherent module. -/
@[stacks 0A1M] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.cohomologyComparison_naturality :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
      [LocallyOfFiniteType f] [QuasiSeparated f] [IsNoetherian B]
      (E : ModuleDerived X) (hE : IsPerfect E)
      (G : CochainComplex (Modules X) ℤ)
      (hG_bounded : CochainComplex.bounded (Modules X) G)
      (hG_coherent : ∀ i : ℤ, (G.X i).IsCoherent)
      (hG_flat : ∀ i : ℤ, Modules.flatOver (G.X i) f)
      (hG_support : ∀ i : ℤ,
        ClosedSubset.ProperOver f (Closeds.closure (Modules.moduleSupport (G.X i))))
      {F F' : Modules B} (φ : F ⟶ F')
      (hF : quasiCoherentModuleProperty B F) (hF' : quasiCoherentModuleProperty B F') (i : ℤ),
      cohomologyComparison f E G F i ≫ cohomologyAb_map (cohomologyTargetMap f E G φ) i =
        cohomologyAb_map (cohomologySourceMap f E G φ) i ≫ cohomologyComparison f E G F' i)

/- Lemma 75.23.1: the isomorphisms commute with the canonical connecting maps
of a short exact sequence of quasi-coherent modules. -/
@[stacks 0A1M] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.cohomologyComparison_boundary :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
      [LocallyOfFiniteType f] [QuasiSeparated f] [IsNoetherian B]
      (E : ModuleDerived X) (hE : IsPerfect E)
      (G : CochainComplex (Modules X) ℤ)
      (hG_bounded : CochainComplex.bounded (Modules X) G)
      (hG_coherent : ∀ i : ℤ, (G.X i).IsCoherent)
      (hG_flat : ∀ i : ℤ, Modules.flatOver (G.X i) f)
      (hG_support : ∀ i : ℤ,
        ClosedSubset.ProperOver f (Closeds.closure (Modules.moduleSupport (G.X i))))
      (s : ShortComplex (Modules B)) (hs : s.ShortExact)
      (hF₁ : quasiCoherentModuleProperty B s.X₁)
      (hF₂ : quasiCoherentModuleProperty B s.X₂)
      (hF₃ : quasiCoherentModuleProperty B s.X₃) (i : ℤ),
      cohomologyComparison f E G s.X₃ i ≫
          cohomologyTargetδ f E G s
            (complexTensorPullback_shortExact f G hG_flat s hs) i =
        cohomologySourceδ f E G s
          (hs.map_of_exact (HomologicalComplex.single (Modules B) (up ℤ) 0)) i ≫
          cohomologyComparison f E G s.X₁ (i + 1))
