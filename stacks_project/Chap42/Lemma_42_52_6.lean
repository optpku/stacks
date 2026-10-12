/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap42.Lemma_42_47_11
public import stacks_project.Chap42.Lemma_42_52_6_RankChoose
public import stacks_project.Chap42.Lemma_42_52_6_TensorSituation

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

open RingedSpace.ModuleDerived

section

variable {S : Scheme.{u}} [UniversallyCatenary S]
variable {δ : S → ℤ} [IsDimensionFunction δ]
variable {X : Over S} [LocallyOfFiniteType X.hom]
variable {Z₁ Z₂ W : Scheme.{u}}
variable (i₁ : Z₁ ⟶ X.left) (i₂ : Z₂ ⟶ X.left) (iW : W ⟶ X.left)
variable [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion iW]
variable (j₁ : Over.mk (iW ≫ X.hom) ⟶ Over.mk (i₁ ≫ X.hom))
variable (j₂ : Over.mk (iW ≫ X.hom) ⟶ Over.mk (i₂ ≫ X.hom))
variable (square : IsPullback j₁.left j₂.left i₁ i₂)
variable (intersection : j₂ ≫ (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) =
  (Over.homMk iW rfl : Over.mk (iW ≫ X.hom) ⟶ X))
variable [KFlat.HomotopyTensorDescends X.left.toRingedSpace]
variable [KFlat.TensorDescends X.left.toRingedSpace]
variable [KFlat.IsLocalization X.left.toRingedSpace]
variable (classes : ChernClass.Theory δ X.hom)
variable (F₁ F₂ : RingedSpace.ModuleDerived X.left.toRingedSpace)
variable (situation₁ : Situation S δ X i₁ F₁ 0 .vanishing)
variable (situation₂ : Situation S δ X i₂ F₂ 0 .vanishing)

/-- Lemma 42.52.6 (1): the first localized Chern class of `F₁ ⊗ᴸ F₂` on
`Z₁ ∩ Z₂` is `r₁ c₁(F₂) + c₁(F₁) r₂`. -/
@[stacks 0FBF]
theorem chernClass_tensor_one :
    let tensorSituation := Situation.tensorOnIntersection i₁ i₂ iW j₁ j₂ square
      intersection F₁ F₂ situation₁ situation₂
    chernClass iW classes (CategoryTheory.MonoidalCategory.tensorObj F₁ F₂) tensorSituation.perfect 1
        (tensorSituation.toRankBound 1 (Nat.zero_lt_succ 0)).offCenter
        tensorSituation.finiteness =
      BivariantClass.Nonnegative.castGrading δ (zero_add (1 : ℤ))
        (BivariantClass.intersectionMul δ
          (Over.homMk i₁ rfl : Over.mk (i₁ ≫ X.hom) ⟶ X)
          (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X)
          j₁ j₂ (Over.homMk iW rfl : Over.mk (iW ≫ X.hom) ⟶ X)
          square intersection
          (newtonClass i₁ classes F₁ situation₁.perfect situation₁.offCenter
            situation₁.finiteness 0)
          (chernClass i₂ classes F₂ situation₂.perfect 1
            (situation₂.toRankBound 1 (Nat.zero_lt_succ 0)).offCenter
            situation₂.finiteness)) +
        BivariantClass.Nonnegative.castGrading δ (add_zero (1 : ℤ))
          (BivariantClass.intersectionMul δ
            (Over.homMk i₁ rfl : Over.mk (i₁ ≫ X.hom) ⟶ X)
            (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X)
            j₁ j₂ (Over.homMk iW rfl : Over.mk (iW ≫ X.hom) ⟶ X)
            square intersection
            (chernClass i₁ classes F₁ situation₁.perfect 1
              (situation₁.toRankBound 1 (Nat.zero_lt_succ 0)).offCenter
              situation₁.finiteness)
            (newtonClass i₂ classes F₂ situation₂.perfect situation₂.offCenter
              situation₂.finiteness 0)) := sorry

/-- Lemma 42.52.6 (2): the second localized Chern class of `F₁ ⊗ᴸ F₂` on
`Z₁ ∩ Z₂` has the five-term binomial virtual-rank expansion. -/
@[stacks 0FBF]
theorem chernClass_tensor_two :
    let tensorSituation := Situation.tensorOnIntersection i₁ i₂ iW j₁ j₂ square
      intersection F₁ F₂ situation₁ situation₂
    let r₁ := newtonClass i₁ classes F₁ situation₁.perfect situation₁.offCenter
      situation₁.finiteness 0
    let r₂ := newtonClass i₂ classes F₂ situation₂.perfect situation₂.offCenter
      situation₂.finiteness 0
    let c₁₁ := chernClass i₁ classes F₁ situation₁.perfect 1
      (situation₁.toRankBound 1 (Nat.zero_lt_succ 0)).offCenter situation₁.finiteness
    let c₁₂ := chernClass i₂ classes F₂ situation₂.perfect 1
      (situation₂.toRankBound 1 (Nat.zero_lt_succ 0)).offCenter situation₂.finiteness
    chernClass iW classes (CategoryTheory.MonoidalCategory.tensorObj F₁ F₂) tensorSituation.perfect 2
        (tensorSituation.toRankBound 2 (Nat.zero_lt_succ 1)).offCenter
        tensorSituation.finiteness =
      BivariantClass.Nonnegative.castGrading δ (zero_add (2 : ℤ))
        (BivariantClass.intersectionMul δ
          (Over.homMk i₁ rfl : Over.mk (i₁ ≫ X.hom) ⟶ X)
          (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X)
          j₁ j₂ (Over.homMk iW rfl : Over.mk (iW ≫ X.hom) ⟶ X)
          square intersection r₁
          (chernClass i₂ classes F₂ situation₂.perfect 2
            (situation₂.toRankBound 2 (Nat.zero_lt_succ 1)).offCenter
            situation₂.finiteness)) +
        BivariantClass.Nonnegative.castGrading δ (add_zero (2 : ℤ))
          (BivariantClass.intersectionMul δ
            (Over.homMk i₁ rfl : Over.mk (i₁ ≫ X.hom) ⟶ X)
            (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X)
            j₁ j₂ (Over.homMk iW rfl : Over.mk (iW ≫ X.hom) ⟶ X)
            square intersection
            (chernClass i₁ classes F₁ situation₁.perfect 2
              (situation₁.toRankBound 2 (Nat.zero_lt_succ 1)).offCenter
              situation₁.finiteness) r₂) +
        BivariantClass.Nonnegative.castGrading δ (Nat.cast_add 0 2).symm
          (BivariantClass.intersectionMul δ
            (Over.homMk i₁ rfl : Over.mk (i₁ ≫ X.hom) ⟶ X)
            (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X)
            j₁ j₂ (Over.homMk iW rfl : Over.mk (iW ≫ X.hom) ⟶ X)
            square intersection (rankChoose i₁ classes F₁ situation₁ 2)
            (BivariantClass.Nonnegative.castGrading δ (Nat.cast_add 1 1).symm
              (BivariantClass.Cutoff.relativeMul δ
                (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) 1 1 c₁₂ c₁₂))) +
        (BivariantClass.Nonnegative.castGrading δ (Nat.cast_add 1 1).symm
            (BivariantClass.intersectionMul δ
              (Over.homMk i₁ rfl : Over.mk (i₁ ≫ X.hom) ⟶ X)
              (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X)
              j₁ j₂ (Over.homMk iW rfl : Over.mk (iW ≫ X.hom) ⟶ X)
              square intersection
              (BivariantClass.Nonnegative.castGrading δ (Nat.cast_add 0 1).symm
                (BivariantClass.Cutoff.relativeMul δ
                  (Over.homMk i₁ rfl : Over.mk (i₁ ≫ X.hom) ⟶ X) 0 1 r₁ c₁₁))
              (BivariantClass.Nonnegative.castGrading δ (Nat.cast_add 0 1).symm
                (BivariantClass.Cutoff.relativeMul δ
                  (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) 0 1 r₂ c₁₂))) -
          BivariantClass.Nonnegative.castGrading δ (Nat.cast_add 1 1).symm
            (BivariantClass.intersectionMul δ
              (Over.homMk i₁ rfl : Over.mk (i₁ ≫ X.hom) ⟶ X)
              (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X)
              j₁ j₂ (Over.homMk iW rfl : Over.mk (iW ≫ X.hom) ⟶ X)
              square intersection c₁₁ c₁₂)) +
        BivariantClass.Nonnegative.castGrading δ (Nat.cast_add 2 0).symm
          (BivariantClass.intersectionMul δ
            (Over.homMk i₁ rfl : Over.mk (i₁ ≫ X.hom) ⟶ X)
            (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X)
            j₁ j₂ (Over.homMk iW rfl : Over.mk (iW ≫ X.hom) ⟶ X)
            square intersection
            (BivariantClass.Nonnegative.castGrading δ (Nat.cast_add 1 1).symm
              (BivariantClass.Cutoff.relativeMul δ
                (Over.homMk i₁ rfl : Over.mk (i₁ ≫ X.hom) ⟶ X) 1 1 c₁₁ c₁₁))
            (rankChoose i₂ classes F₂ situation₂ 2)) := sorry

/-- Lemma 42.52.6 (3): the localized Chern character of `F₁ ⊗ᴸ F₂` is the
componentwise rational intersection product of the two localized characters. -/
@[stacks 0FBF]
theorem character_tensor :
    let tensorSituation := Situation.tensorOnIntersection i₁ i₂ iW j₁ j₂ square
      intersection F₁ F₂ situation₁ situation₂
    character iW classes (CategoryTheory.MonoidalCategory.tensorObj F₁ F₂) tensorSituation.perfect
        tensorSituation.offCenter tensorSituation.finiteness =
      fun p ↦ ∑ ij : Finset.antidiagonal p,
        TensorProduct.tmul ℤ
          (BivariantClass.Nonnegative.castGrading δ
            (BivariantClass.Nonnegative.antidiagonalDegree p ij)
            (BivariantClass.intersectionMul δ
              (Over.homMk i₁ rfl : Over.mk (i₁ ≫ X.hom) ⟶ X)
              (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X)
              j₁ j₂ (Over.homMk iW rfl : Over.mk (iW ≫ X.hom) ⟶ X)
              square intersection
              (newtonClass i₁ classes F₁ situation₁.perfect situation₁.offCenter
                situation₁.finiteness ij.1.1)
              (newtonClass i₂ classes F₂ situation₂.perfect situation₂.offCenter
                situation₂.finiteness ij.1.2)))
          (((ij.1.1.factorial : ℚ)⁻¹) * ((ij.1.2.factorial : ℚ)⁻¹)) := sorry

/-- Lemma 42.52.6 (4): the degree-`p` localized Newton class of `F₁ ⊗ᴸ F₂`
is the binomial antidiagonal convolution of the localized Newton classes of the factors. -/
@[stacks 0FBF]
theorem newtonClass_tensor (p : ℕ) :
    let tensorSituation := Situation.tensorOnIntersection i₁ i₂ iW j₁ j₂ square
      intersection F₁ F₂ situation₁ situation₂
    newtonClass iW classes (CategoryTheory.MonoidalCategory.tensorObj F₁ F₂) tensorSituation.perfect
        tensorSituation.offCenter tensorSituation.finiteness p =
      ∑ ij : Finset.antidiagonal p, p.choose ij.1.1 •
        BivariantClass.Nonnegative.castGrading δ
          (BivariantClass.Nonnegative.antidiagonalDegree p ij)
          (BivariantClass.intersectionMul δ
            (Over.homMk i₁ rfl : Over.mk (i₁ ≫ X.hom) ⟶ X)
            (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X)
            j₁ j₂ (Over.homMk iW rfl : Over.mk (iW ≫ X.hom) ⟶ X)
            square intersection
            (newtonClass i₁ classes F₁ situation₁.perfect situation₁.offCenter
              situation₁.finiteness ij.1.1)
            (newtonClass i₂ classes F₂ situation₂.perfect situation₂.offCenter
              situation₂.finiteness ij.1.2)) := sorry

end

end AlgebraicGeometry.LocalizedChern


