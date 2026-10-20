/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver
public import stacks_project.Chap99.Situation_99_16_3_Category

/-!
# Lemma 99.16.6

In Situation 99.16.3 the functor `p : Complexes_{X/B} ⟶ (Sch/S)_fppf` is a stack
in groupoids.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

namespace AlgebraicGeometry.AlgebraicSpace.Complexes

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}



/-- Lemma 99.16.6: in Situation 99.16.3, with `f : X ⟶ B` proper, flat, and of
finite presentation, the projection `p : Complexes f ⟶ Over S`, `(T, g, E) ↦ T`,
is a stack in groupoids over `(Sch/S)_fppf`. Hom-types of `Obj f` live in
`Type (u + 1)`, so this cannot land in `GroupoidsOver S`. -/
@[stacks 0DLH]
instance instIsStackInGroupoids (f : X ⟶ B)
    [∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      let Z := (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding
      DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Z)] [Proper f] [Flat f] [FinitePresentation f] :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) (p f) := sorry

/-- The projection `p f` is a stack on the site `(Sch/S)_fppf`. -/
theorem p_isStackOnSite (f : X ⟶ B)
    [∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      let Z := (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding
      DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Z)] [Proper f] [Flat f] [FinitePresentation f] :
    IsStack.OnSite (Scheme.fppfTopology.over S) (p f) := sorry

end AlgebraicGeometry.AlgebraicSpace.Complexes
