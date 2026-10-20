module

public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap108.Lemma_108_4_1_Affine
public import stacks_project.Chap108.Lemma_108_4_1_Diagonal
public import stacks_project.Chap108.Lemma_108_4_1_FinitePresentation
public import stacks_project.Chap108.Lemma_108_12_1_Map

/-!
# Lemma 108.12.1

The relative diagonal of the stack of complexes over `B` is affine and of
finite presentation.
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

/-- Lemma 108.12.1 (1): the relative diagonal `CohStack.Hom.diagonal (toBase f)` of
`Complexes_{X/B}` over `B` is affine. -/
@[stacks 0DPW]
instance instAffine_diagonal (f : X ⟶ B)
    [chartDerived : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [chartTensor : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      let Z := (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding
      DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Z)]
    [Proper f] [Flat f]
    [FinitePresentation f] :
    CohStack.Hom.Affine (CohStack.Hom.diagonal (toBase f)) :=
  sorry

/-- Lemma 108.12.1 (2): the relative diagonal `CohStack.Hom.diagonal (toBase f)` of
`Complexes_{X/B}` over `B` is of finite presentation. -/
@[stacks 0DPW]
instance instFinitePresentation_diagonal (f : X ⟶ B)
    [chartDerived : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [chartTensor : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      let Z := (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding
      DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Z)]
    [Proper f] [Flat f]
    [FinitePresentation f] :
    CohStack.Hom.FinitePresentation (CohStack.Hom.diagonal (toBase f)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Complexes
