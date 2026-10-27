/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.BivariantClass.Gysin.Section
public import stacks_project.Chap42.Lemma_42_55_3_NormalClass
public import stacks_project.Chap42.Situation_42_7_1

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 42.59.2: a section of a smooth morphism is a regular immersion and its Gysin
class composed with smooth flat pullback is the completed identity. The datum `D` is a
chosen model of deformation to the normal cone; canonical production is a library follow-up. -/
@[stacks 0FF1] #check
  (AlgebraicGeometry.BivariantClass.gysin_section_comp_flatPullback_eq_oneOfRankLoci :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
      {X P : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType P.hom]
      (p : P ⟶ X) [Smooth p.left] (s : X ⟶ P) (hs : s ≫ p = 𝟙 X)
      (D : BivariantClass.Gysin.SectionSpecializationOfRankLoci p s hs),
      IsRegularImmersion s.left ∧ ∀ n : ℤ,
        BivariantClass.Gysin.sectionCompositeDegree δ p s hs D n =
          if h : n = 0 then h.symm ▸ BivariantClass.oneOver δ X
          else BivariantClass.pointwiseZero δ (𝟙 X) n)
