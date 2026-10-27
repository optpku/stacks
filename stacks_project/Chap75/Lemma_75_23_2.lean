/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.ProjectionFormula.Ext
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.InternalHom.ClosedPresentation
import StacksCheckRecall

/-! # Functorial Ext projection isomorphisms and their connecting maps -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived.ExtProjectionFormula
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory.DerivedCategory CategoryTheory.Limits ComplexShape TopologicalSpace

universe u

/- Lemma 75.23.2. For quasi-coherent coefficients, the canonical Ext projection
comparison is an isomorphism in every integer degree. -/
@[stacks 08JN] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.ExtProjectionFormula.comparison_isIso :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
      (f : X ⟶ B) [LocallyOfFiniteType f] [QuasiSeparated f] [IsNoetherian B]
      (E : ModuleDerived X) (hE : IsPerfect E)
      (G : CochainComplex (Modules X) ℤ)
      (hG_bounded : CochainComplex.bounded (Modules X) G)
      (hG_coherent : ∀ i : ℤ, (G.X i).IsCoherent)
      (hG_flat : ∀ i : ℤ, Modules.flatOver (G.X i) f)
      (hG_support : ∀ i : ℤ, ClosedSubset.ProperOver f
        (Closeds.closure (Modules.moduleSupport (G.X i))))
      (F : Modules B) (hF : quasiCoherentModuleProperty B F) (i : ℤ),
      IsIso (comparison f E G F i))

#check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.ExtProjectionFormula.comparison_naturality :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
      (f : X ⟶ B) [LocallyOfFiniteType f] [QuasiSeparated f] [IsNoetherian B]
      (E : ModuleDerived X) (hE : IsPerfect E)
      (G : CochainComplex (Modules X) ℤ)
      (hG_bounded : CochainComplex.bounded (Modules X) G)
      (hG_coherent : ∀ i : ℤ, (G.X i).IsCoherent)
      (hG_flat : ∀ i : ℤ, Modules.flatOver (G.X i) f)
      (hG_support : ∀ i : ℤ, ClosedSubset.ProperOver f
        (Closeds.closure (Modules.moduleSupport (G.X i))))
      {F F' : Modules B} (φ : F ⟶ F')
      (hF : quasiCoherentModuleProperty B F) (hF' : quasiCoherentModuleProperty B F') (i : ℤ),
      comparison f E G F i ≫ cohomologyAb_map (targetMap f E G φ) i =
        cohomologyAb_map (sourceMap f E G φ) i ≫ comparison f E G F' i)

#check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.ExtProjectionFormula.comparison_boundary :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
      (f : X ⟶ B) [LocallyOfFiniteType f] [QuasiSeparated f] [IsNoetherian B]
      (E : ModuleDerived X) (hE : IsPerfect E)
      (G : CochainComplex (Modules X) ℤ)
      (hG_bounded : CochainComplex.bounded (Modules X) G)
      (hG_coherent : ∀ i : ℤ, (G.X i).IsCoherent)
      (hG_flat : ∀ i : ℤ, Modules.flatOver (G.X i) f)
      (hG_support : ∀ i : ℤ, ClosedSubset.ProperOver f
        (Closeds.closure (Modules.moduleSupport (G.X i))))
      (s : ShortComplex (Modules B)) (hs : s.ShortExact)
      (hF₁ : quasiCoherentModuleProperty B s.X₁)
      (hF₂ : quasiCoherentModuleProperty B s.X₂)
      (hF₃ : quasiCoherentModuleProperty B s.X₃) (i : ℤ),
      comparison f E G s.X₃ i ≫
          targetδ f E G s (complexTensorPullback_shortExact f G hG_flat s hs) i =
        sourceδ f E G s hs i ≫ comparison f E G s.X₁ (i + 1))
