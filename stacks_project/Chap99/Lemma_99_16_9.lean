/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import stacks_project.Chap98.Definition_98_5_1_Comparison
public import stacks_project.Chap99.Lemma_99_16_4
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 99.16.9

Restriction of `Complexes` along a finite-order-thickening-plus-affine pushout
in `Over S` is an equivalence of fibre categories.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor Limits
open AlgebraicGeometry.AlgebraicSpace.Complexes

noncomputable section

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

namespace AlgebraicGeometry.AlgebraicSpace.Complexes

/-- Lemma 99.16.9: in Situation 99.16.3, if `i : Z ⟶ Z'` is a finite-order
thickening and `g : Z ⟶ Y` is affine, and `h` exhibits the square `Z`, `Z'`,
`Y`, `Y'` as a pushout in `Over S` (More on Morphisms, Lemma 37.14.3), then
the functor of fibre categories `restrictionComparison (p f) h.w`, i.e.
`Complexes_{X/B, Y'} ⥤ Complexes_{X/B, Y} ×_{Complexes_{X/B, Z}} Complexes_{X/B, Z'}`,
identifying `Complexes_{X/B, T}` with `(p f).Fiber T` and the source fibre
product with `(Chosen.reindex (p f) g) ⊡ (Chosen.reindex (p f) i)`, is an
equivalence. -/
@[stacks 0DLK]
instance restrictionComparison.instIsEquivalence {S : Scheme.{u}}
    {X B : AlgebraicSpace S} (f : X ⟶ B)
    [∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      let Z := (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding
      DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Z)]
    [Proper f] [Flat f] [FinitePresentation f]
    {Z Z' Y Y' : Over S} {i : Z ⟶ Z'} {g : Z ⟶ Y} {inl : Z' ⟶ Y'} {inr : Y ⟶ Y'}
    [IsFiniteOrderThickening i.left] [IsAffineHom g.left] (h : IsPushout i g inl inr) :
    (restrictionComparison (p f) h.w).IsEquivalence := sorry

end AlgebraicGeometry.AlgebraicSpace.Complexes
