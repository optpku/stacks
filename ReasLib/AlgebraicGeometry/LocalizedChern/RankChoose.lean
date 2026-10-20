/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocalizedChern.GlobalProducer
public import ReasLib.AlgebraicGeometry.LocalizedChern.Deformation
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback.Composition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback.Triangulated
public import ReasLib.AlgebraicGeometry.LocalizedChern.ClosedCover.Constructed
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Derived.VirtualRank
public import ReasLib.AlgebraicGeometry.BivariantClass.PushforwardComp

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section
universe u

namespace AlgebraicGeometry.LocalizedChern

variable {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
  {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
  (i : Z ⟶ X.left) [IsClosedImmersion i]
  (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
  (situation : Situation S δ X i E 0 .vanishing)

-- Local declaration justification (metaprogramming implementation): expose the private
-- vanishing proof to the Prop-valued descent law of the public construction.
set_option backward.privateInPublic true in
/-- Positive generalized binomial virtual-rank classes vanish on the
intersection of the graph center with its vanishing locus. -/
private theorem rankChoose_intersectionVanishes (n : ℕ) (hn : 0 < n) :
    Constructed.IntersectionVanishes δ
      (GlobalProducer.firstMap δ X i E 0 .vanishing situation) (GlobalProducer.centerMap δ X i E 0 .vanishing situation).left 0
      (BivariantClass.restrict δ (GlobalProducer.centerDisplayIso δ X i E 0 .vanishing situation).inv
      (𝟙 _) (GlobalProducer.centerDisplayIso δ X i E 0 .vanishing situation).inv IsPullback.of_id_snd 0
      (ChernClass.Derived.rankChoose δ (GlobalProducer.center δ X i E 0 .vanishing situation).hom
        (GlobalProducer.centerInput δ X i E 0 .vanishing situation)
        (GlobalProducer.centerInput_perfect δ X i E 0 .vanishing situation) n)) := by
  intro V hV v₂ hv₂ v₁ intersection k
  let a := v₂ ≫ (GlobalProducer.centerDisplayIso δ X i E 0 .vanishing situation).inv
  let j := (GlobalProducer.centerMap δ X i E 0 .vanishing situation).left ≫
    (BivariantClass.GysinAtInfinity.infinityInclusion X
      (GlobalProducer.b δ X i E 0 .vanishing situation)).left
  let t := GlobalProducer.firstMap δ X i E 0 .vanishing situation ≫
    (BivariantClass.GysinAtInfinity.infinityInclusion X
      (GlobalProducer.b δ X i E 0 .vanishing situation)).left
  have ht : IsZero ((RingedSpace.modulePullbackDerived t.toShHom).obj
      (GlobalProducer.Q δ X i E 0 .vanishing situation)) :=
    GlobalProducer.restrictionOnTprime E 0 .vanishing situation
  have maps : a.left ≫ j = v₁ ≫ t := by
    change (v₂.left ≫ (𝟙 _)) ≫
        ((GlobalProducer.centerMap δ X i E 0 .vanishing situation).left ≫ _) = _
    rw [Category.comp_id, ← Category.assoc, intersection, Category.assoc]
  have hz : IsZero ((RingedSpace.modulePullbackDerived a.left.toShHom).obj
      (GlobalProducer.centerInput δ X i E 0 .vanishing situation)) := by
    let leftIso := (RingedSpace.modulePullbackDerived.compIso a.left.toShHom j.toShHom
      (RingedSpace.modulePullbackDerived.compComparison_isIso _ _)).app
      (GlobalProducer.Q δ X i E 0 .vanishing situation)
    apply leftIso.isZero_iff.mpr
    let rightIso := (RingedSpace.modulePullbackDerived.compIso v₁.toShHom t.toShHom
      (RingedSpace.modulePullbackDerived.compComparison_isIso _ _)).app
      (GlobalProducer.Q δ X i E 0 .vanishing situation)
    have pulledZero : IsZero ((RingedSpace.modulePullbackDerived v₁.toShHom).obj
        ((RingedSpace.modulePullbackDerived t.toShHom).obj
          (GlobalProducer.Q δ X i E 0 .vanishing situation))) := by
      -- Local instance justification (proof-local temporary data): install the selected canonical shift comparison for this derived pullback so its exactness theorem applies.
      letI : (RingedSpace.modulePullbackDerived v₁.toShHom).CommShift ℤ :=
        RingedSpace.modulePullbackDerived.commShift v₁.toShHom
      -- Local instance justification (proof-local temporary data): exactness with the selected shift comparison lets this derived pullback preserve the given zero object.
      letI : (RingedSpace.modulePullbackDerived v₁.toShHom).IsTriangulated :=
        RingedSpace.modulePullbackDerived.isTriangulated v₁.toShHom
      exact (RingedSpace.modulePullbackDerived v₁.toShHom).map_isZero ht
    have hr := rightIso.isZero_iff.mp pulledZero
    change IsZero ((RingedSpace.modulePullbackDerived (a.left ≫ j).toShHom).obj _) at ⊢
    rw [maps]
    exact hr
  exact ChernClass.Derived.rankChoose_cap_eq_zero_of_isZero_pullback δ
    (GlobalProducer.center δ X i E 0 .vanishing situation).hom
    (GlobalProducer.centerInput δ X i E 0 .vanishing situation)
    (GlobalProducer.centerInput_perfect δ X i E 0 .vanishing situation)
    n hn a (𝟙 V) a (IsPullback.of_id_snd) hz k

-- Local declaration justification (metaprogramming implementation): the exposed
-- quotient construction refers to its private Prop-valued vanishing law.
set_option backward.privateInPublic true in
/-- The positive generalized binomial coefficient of virtual rank, localized
to the closed center by graph deformation and closed-cover descent. -/
def rankChoose (n : ℕ) (hn : 0 < n) :
    BivariantClass δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) 0 :=
  let ambient := BivariantClass.restrict δ (GlobalProducer.centerDisplayIso δ X i E 0 .vanishing situation).inv
      (𝟙 _) (GlobalProducer.centerDisplayIso δ X i E 0 .vanishing situation).inv IsPullback.of_id_snd 0
      (ChernClass.Derived.rankChoose δ (GlobalProducer.center δ X i E 0 .vanishing situation).hom
        (GlobalProducer.centerInput δ X i E 0 .vanishing situation)
        (GlobalProducer.centerInput_perfect δ X i E 0 .vanishing situation) n)
  let localizedDisplay := Constructed.localized δ
    (GlobalProducer.firstMap δ X i E 0 .vanishing situation) (GlobalProducer.centerMap δ X i E 0 .vanishing situation).left 0
    ambient (GlobalProducer.cover δ X i E 0 .vanishing situation)
    (rankChoose_intersectionVanishes i E situation n hn)
  let infinityClass := BivariantClass.restrict δ
    (GlobalProducer.centerDisplayIso δ X i E 0 .vanishing situation).hom
    (GlobalProducer.centerMap δ X i E 0 .vanishing situation) (𝟙 (GlobalProducer.infinity δ X i E 0 .vanishing situation))
    (GlobalProducer.centerPresentationSquare δ X i E 0 .vanishing situation) 0 localizedDisplay
  @BivariantClass.pushforwardComp S _ δ _
    (GlobalProducer.center δ X i E 0 .vanishing situation) (Over.mk (i ≫ X.hom))
    (GlobalProducer.infinity δ X i E 0 .vanishing situation) X
    (GlobalProducer.center_finiteType δ X i E 0 .vanishing situation) inferInstance
    (GlobalProducer.infinity_finiteType δ X i E 0 .vanishing situation) inferInstance
    (pullback.snd (GlobalProducer.infinityToX δ X i E 0 .vanishing situation)
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X))
    (by
      refine @instIsProperPullbackSnd _ _ _ _ _ ?_ _
      change IsProper
        ((BivariantClass.GysinAtInfinity.infinityInclusion X
            (GlobalProducer.b δ X i E 0 .vanishing situation)).left ≫
          (BivariantClass.GysinAtInfinity.toX X
            (GlobalProducer.b δ X i E 0 .vanishing situation)).left)
      infer_instance)
    (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)
    (GlobalProducer.centerMap δ X i E 0 .vanishing situation)
    (GlobalProducer.infinityToX δ X i E 0 .vanishing situation) pullback.condition 0 infinityClass
    (@BivariantClass.gysinAtInfinity S _ _ δ _ X _
      (GlobalProducer.b δ X i E 0 .vanishing situation)
      (GlobalProducer.b_proper δ X i E 0 .vanishing situation)
      (GlobalProducer.b_affine_iso δ X i E 0 .vanishing situation))

-- Local declaration justification (metaprogramming implementation): the exposed
-- quotient construction refers to its private Prop-valued vanishing law.
set_option backward.privateInPublic true in
/-- The localized binomial virtual-rank class is the proper pushforward of
its closed-cover quotient descent composed with Gysin at infinity. -/
theorem rankChoose_spec (n : ℕ) (hn : 0 < n) :
    rankChoose i E situation n hn =
  let ambient := BivariantClass.restrict δ (GlobalProducer.centerDisplayIso δ X i E 0 .vanishing situation).inv
      (𝟙 _) (GlobalProducer.centerDisplayIso δ X i E 0 .vanishing situation).inv IsPullback.of_id_snd 0
      (ChernClass.Derived.rankChoose δ (GlobalProducer.center δ X i E 0 .vanishing situation).hom
        (GlobalProducer.centerInput δ X i E 0 .vanishing situation)
        (GlobalProducer.centerInput_perfect δ X i E 0 .vanishing situation) n)
  let localizedDisplay := Constructed.localized δ
    (GlobalProducer.firstMap δ X i E 0 .vanishing situation) (GlobalProducer.centerMap δ X i E 0 .vanishing situation).left 0
    ambient (GlobalProducer.cover δ X i E 0 .vanishing situation)
    (rankChoose_intersectionVanishes i E situation n hn)
  let infinityClass := BivariantClass.restrict δ
    (GlobalProducer.centerDisplayIso δ X i E 0 .vanishing situation).hom
    (GlobalProducer.centerMap δ X i E 0 .vanishing situation) (𝟙 (GlobalProducer.infinity δ X i E 0 .vanishing situation))
    (GlobalProducer.centerPresentationSquare δ X i E 0 .vanishing situation) 0 localizedDisplay
  @BivariantClass.pushforwardComp S _ δ _
    (GlobalProducer.center δ X i E 0 .vanishing situation) (Over.mk (i ≫ X.hom))
    (GlobalProducer.infinity δ X i E 0 .vanishing situation) X
    (GlobalProducer.center_finiteType δ X i E 0 .vanishing situation) inferInstance
    (GlobalProducer.infinity_finiteType δ X i E 0 .vanishing situation) inferInstance
    (pullback.snd (GlobalProducer.infinityToX δ X i E 0 .vanishing situation)
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X))
    (by
      refine @instIsProperPullbackSnd _ _ _ _ _ ?_ _
      change IsProper
        ((BivariantClass.GysinAtInfinity.infinityInclusion X
            (GlobalProducer.b δ X i E 0 .vanishing situation)).left ≫
          (BivariantClass.GysinAtInfinity.toX X
            (GlobalProducer.b δ X i E 0 .vanishing situation)).left)
      infer_instance)
    (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)
    (GlobalProducer.centerMap δ X i E 0 .vanishing situation)
    (GlobalProducer.infinityToX δ X i E 0 .vanishing situation) pullback.condition 0 infinityClass
    (@BivariantClass.gysinAtInfinity S _ _ δ _ X _
      (GlobalProducer.b δ X i E 0 .vanishing situation)
      (GlobalProducer.b_proper δ X i E 0 .vanishing situation)
      (GlobalProducer.b_affine_iso δ X i E 0 .vanishing situation)) := rfl

/-- Proper pushforward of the localized positive binomial virtual-rank class
recovers the corresponding ambient generalized binomial class. -/
theorem rankChoose_pushforward (n : ℕ) (hn : 0 < n) :
    BivariantClass.properPushforwardToTarget δ
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ Over.mk X.hom) 0
        (rankChoose i E situation n hn) =
      ChernClass.Derived.rankChoose δ X.hom E situation.perfect n := by
  sorry

end AlgebraicGeometry.LocalizedChern
