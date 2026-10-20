module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.LocalizedChern.Tensor

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section
universe u

namespace AlgebraicGeometry.LocalizedChern

open RingedSpace.ModuleDerived

/- Lemma 42.52.6 -/
@[stacks 0FBF] #check (AlgebraicGeometry.LocalizedChern.chernClass_tensor_one :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S]
{δ : S → ℤ} [IsDimensionFunction δ]
{X : Over S} [LocallyOfFiniteType X.hom]
{Z₁ Z₂ W : Scheme.{u}}
(i₁ : Z₁ ⟶ X.left) (i₂ : Z₂ ⟶ X.left) (iW : W ⟶ X.left)
[IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion iW]
(j₁ : Over.mk (iW ≫ X.hom) ⟶ Over.mk (i₁ ≫ X.hom))
(j₂ : Over.mk (iW ≫ X.hom) ⟶ Over.mk (i₂ ≫ X.hom))
(square : IsPullback j₁.left j₂.left i₁ i₂)
(intersection : j₂ ≫ (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) =
  (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X))
[KFlat.HomotopyTensorDescends X.left.toRingedSpace]
[KFlat.TensorDescends X.left.toRingedSpace]
[KFlat.IsLocalization X.left.toRingedSpace]
(classes : ChernClass.Theory δ X.hom)
(F₁ F₂ : RingedSpace.ModuleDerived X.left.toRingedSpace)
(situation₁ : Situation S δ X i₁ F₁ 0 .vanishing)
(situation₂ : Situation S δ X i₂ F₂ 0 .vanishing),
    let tensorSituation := Situation.tensorOnIntersection i₁ i₂ iW j₁ j₂ square
      intersection F₁ F₂ situation₁ situation₂
    chernClass iW classes (CategoryTheory.MonoidalCategory.tensorObj F₁ F₂) tensorSituation.perfect 1
        (Scheme.ModuleDerived.rankBound_of_isZero tensorSituation.offCenter (Nat.zero_lt_succ 0))
        tensorSituation.finiteness =
      BivariantClass.pointwiseAdd δ (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X) 1
        (BivariantClass.Nonnegative.castGrading δ (zero_add (1 : ℤ))
        (BivariantClass.intersectionMul δ
          (Over.homMk i₁ rfl : Over.mk (i₁ ≫ X.hom) ⟶ X)
          (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X)
          j₁ j₂ (Over.homMk iW rfl : Over.mk (iW ≫ X.hom) ⟶ X)
          square intersection
          (newtonClass i₁ classes F₁ situation₁.perfect situation₁.offCenter
            situation₁.finiteness 0)
          (chernClass i₂ classes F₂ situation₂.perfect 1
            (Scheme.ModuleDerived.rankBound_of_isZero situation₂.offCenter (Nat.zero_lt_succ 0))
            situation₂.finiteness)))
        (BivariantClass.Nonnegative.castGrading δ (add_zero (1 : ℤ))
          (BivariantClass.intersectionMul δ
            (Over.homMk i₁ rfl : Over.mk (i₁ ≫ X.hom) ⟶ X)
            (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X)
            j₁ j₂ (Over.homMk iW rfl : Over.mk (iW ≫ X.hom) ⟶ X)
            square intersection
            (chernClass i₁ classes F₁ situation₁.perfect 1
              (Scheme.ModuleDerived.rankBound_of_isZero situation₁.offCenter (Nat.zero_lt_succ 0))
              situation₁.finiteness)
            (newtonClass i₂ classes F₂ situation₂.perfect situation₂.offCenter
              situation₂.finiteness 0))))

/- Lemma 42.52.6 -/
@[stacks 0FBF] #check (AlgebraicGeometry.LocalizedChern.chernClass_tensor_two :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S]
{δ : S → ℤ} [IsDimensionFunction δ]
{X : Over S} [LocallyOfFiniteType X.hom]
{Z₁ Z₂ W : Scheme.{u}}
(i₁ : Z₁ ⟶ X.left) (i₂ : Z₂ ⟶ X.left) (iW : W ⟶ X.left)
[IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion iW]
(j₁ : Over.mk (iW ≫ X.hom) ⟶ Over.mk (i₁ ≫ X.hom))
(j₂ : Over.mk (iW ≫ X.hom) ⟶ Over.mk (i₂ ≫ X.hom))
(square : IsPullback j₁.left j₂.left i₁ i₂)
(intersection : j₂ ≫ (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) =
  (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X))
[KFlat.HomotopyTensorDescends X.left.toRingedSpace]
[KFlat.TensorDescends X.left.toRingedSpace]
[KFlat.IsLocalization X.left.toRingedSpace]
(classes : ChernClass.Theory δ X.hom)
(F₁ F₂ : RingedSpace.ModuleDerived X.left.toRingedSpace)
(situation₁ : Situation S δ X i₁ F₁ 0 .vanishing)
(situation₂ : Situation S δ X i₂ F₂ 0 .vanishing),
    let tensorSituation := Situation.tensorOnIntersection i₁ i₂ iW j₁ j₂ square
      intersection F₁ F₂ situation₁ situation₂
    let r₁ := newtonClass i₁ classes F₁ situation₁.perfect situation₁.offCenter
      situation₁.finiteness 0
    let r₂ := newtonClass i₂ classes F₂ situation₂.perfect situation₂.offCenter
      situation₂.finiteness 0
    let c₁₁ := chernClass i₁ classes F₁ situation₁.perfect 1
      (Scheme.ModuleDerived.rankBound_of_isZero situation₁.offCenter (Nat.zero_lt_succ 0)) situation₁.finiteness
    let c₁₂ := chernClass i₂ classes F₂ situation₂.perfect 1
      (Scheme.ModuleDerived.rankBound_of_isZero situation₂.offCenter (Nat.zero_lt_succ 0)) situation₂.finiteness
    chernClass iW classes (CategoryTheory.MonoidalCategory.tensorObj F₁ F₂) tensorSituation.perfect 2
        (Scheme.ModuleDerived.rankBound_of_isZero tensorSituation.offCenter (Nat.zero_lt_succ 1))
        tensorSituation.finiteness =
      BivariantClass.pointwiseAdd δ (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X) 2
        (BivariantClass.pointwiseAdd δ (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X) 2
        (BivariantClass.pointwiseAdd δ (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X) 2
        (BivariantClass.pointwiseAdd δ (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X) 2
        (BivariantClass.Nonnegative.castGrading δ (zero_add (2 : ℤ))
        (BivariantClass.intersectionMul δ
          (Over.homMk i₁ rfl : Over.mk (i₁ ≫ X.hom) ⟶ X)
          (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X)
          j₁ j₂ (Over.homMk iW rfl : Over.mk (iW ≫ X.hom) ⟶ X)
          square intersection r₁
          (chernClass i₂ classes F₂ situation₂.perfect 2
            (Scheme.ModuleDerived.rankBound_of_isZero situation₂.offCenter (Nat.zero_lt_succ 1))
            situation₂.finiteness)))
        (BivariantClass.Nonnegative.castGrading δ (add_zero (2 : ℤ))
          (BivariantClass.intersectionMul δ
            (Over.homMk i₁ rfl : Over.mk (i₁ ≫ X.hom) ⟶ X)
            (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X)
            j₁ j₂ (Over.homMk iW rfl : Over.mk (iW ≫ X.hom) ⟶ X)
            square intersection
            (chernClass i₁ classes F₁ situation₁.perfect 2
              (Scheme.ModuleDerived.rankBound_of_isZero situation₁.offCenter (Nat.zero_lt_succ 1))
              situation₁.finiteness) r₂)))
        (BivariantClass.Nonnegative.castGrading δ (Nat.cast_add 0 2).symm
          (BivariantClass.intersectionMul δ
            (Over.homMk i₁ rfl : Over.mk (i₁ ≫ X.hom) ⟶ X)
            (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X)
            j₁ j₂ (Over.homMk iW rfl : Over.mk (iW ≫ X.hom) ⟶ X)
            square intersection (rankChoose i₁ F₁ situation₁ 2 (by decide))
            (BivariantClass.Nonnegative.castGrading δ (Nat.cast_add 1 1).symm
              (BivariantClass.Cutoff.relativeMul δ
                (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) 1 1 c₁₂ c₁₂)))))
        (BivariantClass.pointwiseAdd δ (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X) 2
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
                  (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) 0 1 r₂ c₁₂))))
        (BivariantClass.pointwiseNeg δ (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X) 2
          (BivariantClass.Nonnegative.castGrading δ (Nat.cast_add 1 1).symm
            (BivariantClass.intersectionMul δ
              (Over.homMk i₁ rfl : Over.mk (i₁ ≫ X.hom) ⟶ X)
              (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X)
              j₁ j₂ (Over.homMk iW rfl : Over.mk (iW ≫ X.hom) ⟶ X)
              square intersection c₁₁ c₁₂)))))
        (BivariantClass.Nonnegative.castGrading δ (Nat.cast_add 2 0).symm
          (BivariantClass.intersectionMul δ
            (Over.homMk i₁ rfl : Over.mk (i₁ ≫ X.hom) ⟶ X)
            (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X)
            j₁ j₂ (Over.homMk iW rfl : Over.mk (iW ≫ X.hom) ⟶ X)
            square intersection
            (BivariantClass.Nonnegative.castGrading δ (Nat.cast_add 1 1).symm
              (BivariantClass.Cutoff.relativeMul δ
                (Over.homMk i₁ rfl : Over.mk (i₁ ≫ X.hom) ⟶ X) 1 1 c₁₁ c₁₁))
            (rankChoose i₂ F₂ situation₂ 2 (by decide)))))

/- Lemma 42.52.6 -/
@[stacks 0FBF] #check (AlgebraicGeometry.LocalizedChern.character_tensor :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S]
{δ : S → ℤ} [IsDimensionFunction δ]
{X : Over S} [LocallyOfFiniteType X.hom]
{Z₁ Z₂ W : Scheme.{u}}
(i₁ : Z₁ ⟶ X.left) (i₂ : Z₂ ⟶ X.left) (iW : W ⟶ X.left)
[IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion iW]
(j₁ : Over.mk (iW ≫ X.hom) ⟶ Over.mk (i₁ ≫ X.hom))
(j₂ : Over.mk (iW ≫ X.hom) ⟶ Over.mk (i₂ ≫ X.hom))
(square : IsPullback j₁.left j₂.left i₁ i₂)
(intersection : j₂ ≫ (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) =
  (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X))
[KFlat.HomotopyTensorDescends X.left.toRingedSpace]
[KFlat.TensorDescends X.left.toRingedSpace]
[KFlat.IsLocalization X.left.toRingedSpace]
(classes : ChernClass.Theory δ X.hom)
(F₁ F₂ : RingedSpace.ModuleDerived X.left.toRingedSpace)
(situation₁ : Situation S δ X i₁ F₁ 0 .vanishing)
(situation₂ : Situation S δ X i₂ F₂ 0 .vanishing),
    let tensorSituation := Situation.tensorOnIntersection i₁ i₂ iW j₁ j₂ square
      intersection F₁ F₂ situation₁ situation₂
    rationalCharacter iW classes (CategoryTheory.MonoidalCategory.tensorObj F₁ F₂) tensorSituation.perfect
        tensorSituation.offCenter tensorSituation.finiteness =
      fun p ↦ ∑ ij : Finset.antidiagonal p,
        BivariantClass.Nonnegative.Rational.tensor δ
          (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X) p
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
          (((ij.1.1.factorial : ℚ)⁻¹) * ((ij.1.2.factorial : ℚ)⁻¹)))

/- Lemma 42.52.6 -/
@[stacks 0FBF] #check (AlgebraicGeometry.LocalizedChern.newtonClass_tensor :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S]
{δ : S → ℤ} [IsDimensionFunction δ]
{X : Over S} [LocallyOfFiniteType X.hom]
{Z₁ Z₂ W : Scheme.{u}}
(i₁ : Z₁ ⟶ X.left) (i₂ : Z₂ ⟶ X.left) (iW : W ⟶ X.left)
[IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion iW]
(j₁ : Over.mk (iW ≫ X.hom) ⟶ Over.mk (i₁ ≫ X.hom))
(j₂ : Over.mk (iW ≫ X.hom) ⟶ Over.mk (i₂ ≫ X.hom))
(square : IsPullback j₁.left j₂.left i₁ i₂)
(intersection : j₂ ≫ (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) =
  (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X))
[KFlat.HomotopyTensorDescends X.left.toRingedSpace]
[KFlat.TensorDescends X.left.toRingedSpace]
[KFlat.IsLocalization X.left.toRingedSpace]
(classes : ChernClass.Theory δ X.hom)
(F₁ F₂ : RingedSpace.ModuleDerived X.left.toRingedSpace)
(situation₁ : Situation S δ X i₁ F₁ 0 .vanishing)
(situation₂ : Situation S δ X i₂ F₂ 0 .vanishing)
(p : ℕ),
    let tensorSituation := Situation.tensorOnIntersection i₁ i₂ iW j₁ j₂ square
      intersection F₁ F₂ situation₁ situation₂
    newtonClass iW classes (CategoryTheory.MonoidalCategory.tensorObj F₁ F₂) tensorSituation.perfect
        tensorSituation.offCenter tensorSituation.finiteness p =
      BivariantClass.pointwiseSum δ (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X) (p : ℤ)
        Finset.univ (fun ij : Finset.antidiagonal p ↦
          BivariantClass.pointwiseNsmul δ (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X) (p : ℤ)
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
              situation₂.finiteness ij.1.2))) (p.choose ij.1.1)))

end AlgebraicGeometry.LocalizedChern
