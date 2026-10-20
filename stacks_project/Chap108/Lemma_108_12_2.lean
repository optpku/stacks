/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap108.Lemma_108_4_2_LocallyOfFinitePresentation
public import stacks_project.Chap108.Lemma_108_4_2_QuasiSeparated
public import stacks_project.Chap108.Lemma_108_12_1_Map

/-!
# Lemma 108.12.2

The structure morphism of the stack of complexes over `B` is quasi-separated and
locally of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Complexes
open scoped Bicategory

noncomputable section

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

namespace AlgebraicGeometry.AlgebraicSpace.Complexes

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Lemma 108.12.2 (1): the structure morphism `toBase f : toGroupoids f ⟶
Classifying.toGroupoids B` of `Complexes_{X/B}` is quasi-separated. -/
@[stacks 0DPX]
instance instQuasiSeparated_toBase (f : X ⟶ B)
    [chartDerived : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [chartTensor : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      let Z := (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding
      DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Z)]
    [Proper f] [Flat f]
    [FinitePresentation f] : CohStack.Hom.QuasiSeparated (toBase f) :=
  sorry

/-- Lemma 108.12.2 (2): the structure morphism `toBase f : toGroupoids f ⟶
Classifying.toGroupoids B` of `Complexes_{X/B}` is locally of finite
presentation. -/
@[stacks 0DPX]
instance instLocallyOfFinitePresentation_toBase (f : X ⟶ B)
    [chartDerived : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [chartTensor : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      let Z := (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding
      DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Z)]
    [Proper f] [Flat f]
    [FinitePresentation f] :
    CohStack.Hom.LocallyOfFinitePresentation (toBase f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Complexes
