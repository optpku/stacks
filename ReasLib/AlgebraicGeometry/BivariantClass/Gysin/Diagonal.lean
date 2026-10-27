/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Over
public import ReasLib.AlgebraicGeometry.BivariantClass.Gysin.Section
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BivariantClass

/-- The normal Gysin class of the diagonal of a smooth morphism composed with smooth
pullback along the first projection is the identity in every integer degree, using a
chosen deformation model and allowing locally varying relative dimension. -/
theorem gysin_diagonal_comp_fst_eq_oneOfRankLoci
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [Smooth f.left]
    (D : Gysin.SectionSpecializationOfRankLoci
      (pullback.fst f f) (pullback.diagonal f) (pullback.diagonal_fst f)) (n : ℤ) :
    Gysin.sectionCompositeDegree δ
        (pullback.fst f f) (pullback.diagonal f) (pullback.diagonal_fst f) D n =
      if h : n = 0 then h.symm ▸ oneOver δ X else pointwiseZero δ (𝟙 X) n := sorry

/-- The normal Gysin class of the diagonal of a smooth morphism composed with smooth
pullback along the second projection is the identity in every integer degree, using a
chosen deformation model and allowing locally varying relative dimension. -/
theorem gysin_diagonal_comp_snd_eq_oneOfRankLoci
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [Smooth f.left]
    (D : Gysin.SectionSpecializationOfRankLoci
      (pullback.snd f f) (pullback.diagonal f) (pullback.diagonal_snd f)) (n : ℤ) :
    Gysin.sectionCompositeDegree δ
        (pullback.snd f f) (pullback.diagonal f) (pullback.diagonal_snd f) D n =
      if h : n = 0 then h.symm ▸ oneOver δ X else pointwiseZero δ (𝟙 X) n := sorry

end AlgebraicGeometry.BivariantClass
