/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.BivariantClass.Gysin.Diagonal

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.BivariantClass

/- Lemma 42.60.1 (1): the diagonal Gysin class composed with smooth pullback along
projection 1 is the identity, coefficientwise in every integer degree. -/
@[stacks 0FBS] #check
  (AlgebraicGeometry.BivariantClass.gysin_diagonal_comp_fst_eq_oneOfRankLoci :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
      {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
      (f : X ⟶ Y) [Smooth f.left]
      (D : Gysin.SectionSpecializationOfRankLoci
        (pullback.fst f f) (pullback.diagonal f) (pullback.diagonal_fst f)) (n : ℤ),
      Gysin.sectionCompositeDegree δ
          (pullback.fst f f) (pullback.diagonal f) (pullback.diagonal_fst f) D n =
        if h : n = 0 then h.symm ▸ oneOver δ X else pointwiseZero δ (𝟙 X) n)

/- Lemma 42.60.1 (2): the diagonal Gysin class composed with smooth pullback along
projection 2 is the identity, coefficientwise in every integer degree. -/
@[stacks 0FBS] #check
  (AlgebraicGeometry.BivariantClass.gysin_diagonal_comp_snd_eq_oneOfRankLoci :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
      {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
      (f : X ⟶ Y) [Smooth f.left]
      (D : Gysin.SectionSpecializationOfRankLoci
        (pullback.snd f f) (pullback.diagonal f) (pullback.diagonal_snd f)) (n : ℤ),
      Gysin.sectionCompositeDegree δ
          (pullback.snd f f) (pullback.diagonal f) (pullback.diagonal_snd f) D n =
        if h : n = 0 then h.symm ▸ oneOver δ X else pointwiseZero δ (𝟙 X) n)

end AlgebraicGeometry.BivariantClass
