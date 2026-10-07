module

public import stacks_project.Chap42.Definition_42_50_3_LocalizedClasses
public import stacks_project.Chap42.Lemma_42_46_11_VirtualRank

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/-- A degree-zero class is a localized binomial virtual-rank class when it is obtained
from a valid deformation construction by localizing `rankChoose` at infinity and then
applying `classAtZero`. -/
def IsRankChooseResult
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (situation : Situation S δ X i E 0 .vanishing) (n : ℕ)
    (localized : BivariantClass δ
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) 0) : Prop :=
  ∃ construction : ClassConstruction δ i classes E 0 .vanishing situation,
    ∃ centerFinite : LocallyOfFiniteType (infinityCenter i construction.b).hom,
      ∃ pullbackFinite : LocallyOfFiniteType
          (pullback (BivariantClass.GysinAtInfinity.infinityToX X construction.b)
            (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)).hom,
        ∃ fiberFinite : LocallyOfFiniteType
            (BivariantClass.GysinAtInfinity.infinityFiber X construction.b).hom,
          ∃ closedT : IsClosedImmersion (construction.t' ≫ construction.t),
            ∃ localizedAtInfinity : @BivariantClass S inferInstance δ inferInstance
                (pullback (BivariantClass.GysinAtInfinity.infinityToX X construction.b)
                  (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X))
                (BivariantClass.GysinAtInfinity.infinityFiber X construction.b)
                pullbackFinite fiberFinite
                (pullback.fst (BivariantClass.GysinAtInfinity.infinityToX X construction.b)
                  (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)) 0,
              @IsInfinityLocalizedExtension S inferInstance δ inferInstance X inferInstance
                  Z construction.W construction.T' i inferInstance construction.b
                  construction.b_isProper construction.b_affinePart_isIso
                  construction.infinityCenter_isClosedImmersion
                  (construction.t' ≫ construction.t) closedT 0
                  (@ChernClass.Derived.rankChoose S (infinityCenter i construction.b).left
                    inferInstance δ inferInstance (infinityCenter i construction.b).hom
                    centerFinite (infinityCenterRestriction i construction.b construction.Q)
                    construction.infinityCenter_isPerfect n)
                  localizedAtInfinity ∧
                localized = @classAtZero S inferInstance δ inferInstance X inferInstance
                  Z construction.W i inferInstance construction.b construction.b_isProper
                  construction.b_affinePart_isIso 0 localizedAtInfinity

/-- The canonical localized generalized binomial coefficient of the virtual rank. -/
noncomputable def rankChoose
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (situation : Situation S δ X i E 0 .vanishing) (n : ℕ) :
    BivariantClass δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) 0 :=
  Classical.epsilon (IsRankChooseResult i classes E situation n)

/-- The canonical localized binomial virtual-rank class is represented by a valid
deformation construction. -/
theorem rankChoose_spec
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (situation : Situation S δ X i E 0 .vanishing) (n : ℕ) :
    IsRankChooseResult i classes E situation n
      (rankChoose i classes E situation n) := sorry

/-- Two localized binomial virtual-rank classes obtained from valid deformation
constructions agree. -/
theorem rankChoose_eq_of_result
    {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (situation : Situation S δ X i E 0 .vanishing) (n : ℕ)
    {a b : BivariantClass δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) 0}
    (ha : IsRankChooseResult i classes E situation n a)
    (hb : IsRankChooseResult i classes E situation n b) : a = b := sorry

end AlgebraicGeometry.LocalizedChern
