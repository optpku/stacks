/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Mapping injective resolutions

This file provides the injective counterpart of Mathlib's
`Functor.mapProjectiveResolution`. An additive functor preserving injective objects and
homology sends an injective resolution to an injective resolution.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {A : Type u₁} [Category.{v₁} A] [HasZeroObject A] [Preadditive A]
variable {B : Type u₂} [Category.{v₂} B] [HasZeroObject B] [Preadditive B]
variable [CategoryWithHomology B]

/-- Every term of the image of an injective resolution is injective when the functor preserves
injective objects. -/
theorem mapInjectiveResolution_injective
    (G : A ⥤ B) [G.Additive] [G.PreservesInjectiveObjects]
    {X : A} (I : InjectiveResolution X) (n : ℕ) :
    Injective
      (((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).X n) := sorry

/-- Applying a homology-preserving functor to the augmentation of an injective resolution
again gives a quasi-isomorphism. -/
theorem mapInjectiveResolution_quasiIso
    (G : A ⥤ B) [G.Additive] [G.PreservesHomology]
    {X : A} (I : InjectiveResolution X) :
    QuasiIso
      ((HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℕ) 0).inv.app X ≫
        (G.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι) := sorry

/-- An additive functor preserving injective objects and homology sends an injective resolution
of `X` to an injective resolution of `G.obj X`. -/
noncomputable def mapInjectiveResolution
    (G : A ⥤ B) [G.Additive] [G.PreservesInjectiveObjects] [G.PreservesHomology]
    {X : A} (I : InjectiveResolution X) : InjectiveResolution (G.obj X) where
  cocomplex := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  injective n := mapInjectiveResolution_injective G I n
  ι := (HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℕ) 0).inv.app X ≫
    (G.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι
  quasiIso := mapInjectiveResolution_quasiIso G I

end CategoryTheory.Functor
