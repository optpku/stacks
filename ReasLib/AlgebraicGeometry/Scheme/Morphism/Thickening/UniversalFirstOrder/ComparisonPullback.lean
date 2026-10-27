/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.UniversalFirstOrder.Comparison

/-!
# Comparison pullbacks of universal first-order thickenings

Chosen universal first-order thickenings over a common base determine a canonical ambient
comparison. Pulling back along this comparison gives a universal first-order thickening over
the intermediate closed scheme.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Thickening.IsUniversalFirstOrder

variable {X : Scheme.{u}} (T U : Thickening.Over X)
  [IsUniversalFirstOrder T] [IsUniversalFirstOrder U]
  (i : T.left.left ⟶ U.left.left) (hi : i ≫ U.left.hom = T.left.hom)

/-- The ambient component `Z' ⟶ Y'` of the canonical map between two chosen universal
first-order thickenings over the same base. -/
noncomputable def ambientComparison : T.right.left ⟶ U.right.left :=
  (lift T (CategoryTheory.Over.homMk i hi)).right.left

set_option backward.isDefEq.respectTransparency false in
/-- The ambient comparison and the prescribed map on the closed parts form a commutative
square. -/
theorem ambientComparison_comm :
    i ≫ U.hom.left = T.hom.left ≫ ambientComparison T U i hi := by
  have hleft : (lift T (CategoryTheory.Over.homMk i hi)).left.left = i :=
    congrArg (fun f : T.left ⟶ U.left ↦ f.left)
      (existsUniqueLift T (CategoryTheory.Over.homMk i hi)).choose_spec.1
  simpa only [CategoryTheory.Over.comp_left, hleft, ambientComparison] using
    congrArg (fun f : T.left ⟶ U.right ↦ f.left)
      (MorphismProperty.Arrow.w (lift T (CategoryTheory.Over.homMk i hi)))

/-- The ambient comparison is a morphism over the common base scheme. -/
theorem ambientComparison_over :
    ambientComparison T U i hi ≫ U.right.hom = T.right.hom :=
  CategoryTheory.Over.w (lift T (CategoryTheory.Over.homMk i hi)).right

/-- The ambient comparison is uniquely determined by its commutative-square and
over-the-base equations. -/
theorem ambientComparison_unique (k : T.right.left ⟶ U.right.left)
    (hk_comm : i ≫ U.hom.left = T.hom.left ≫ k)
    (hk_over : k ≫ U.right.hom = T.right.hom) :
    k = ambientComparison T U i hi := by
  let g : T ⟶ U := MorphismProperty.Arrow.homMk
    (CategoryTheory.Over.homMk i hi) (CategoryTheory.Over.homMk k hk_over)
    (by ext; exact hk_comm)
  have hg : g = lift T (CategoryTheory.Over.homMk i hi) :=
    (existsUniqueLift T (CategoryTheory.Over.homMk i hi)).choose_spec.2 g rfl
  exact congrArg (fun f : T ⟶ U ↦ f.right.left) hg

/-- The canonical map from the closed scheme `Z` to the fibre product `Y ×_[Y'] Z'`. -/
noncomputable def comparisonPullbackHom :
    T.left.left ⟶ pullback U.hom.left (ambientComparison T U i hi) :=
  pullback.lift i T.hom.left (ambientComparison_comm T U i hi)

/-- The first projection of the canonical map to `Y ×_[Y'] Z'` is `i`. -/
theorem comparisonPullbackHom_fst :
    comparisonPullbackHom T U i hi ≫
        pullback.fst U.hom.left (ambientComparison T U i hi) = i :=
  pullback.lift_fst _ _ _

/-- The second projection of the canonical map to `Y ×_[Y'] Z'` is the defining map
`Z ⟶ Z'` of `T`. -/
theorem comparisonPullbackHom_snd :
    comparisonPullbackHom T U i hi ≫
        pullback.snd U.hom.left (ambientComparison T U i hi) = T.hom.left :=
  pullback.lift_snd _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The canonical map from `Z` to `Y ×_[Y'] Z'` is a thickening. -/
instance comparisonPullbackHom_isThickening :
    IsThickening (comparisonPullbackHom T U i hi) := by
  letI : IsThickening T.hom.left := T.prop
  letI : IsThickening U.hom.left := U.prop
  let p := pullback.snd U.hom.left (ambientComparison T U i hi)
  letI : IsClosedImmersion (comparisonPullbackHom T U i hi ≫ p) :=
    (comparisonPullbackHom_snd T U i hi).symm ▸ T.prop.toIsClosedImmersion
  letI : IsClosedImmersion (comparisonPullbackHom T U i hi) :=
    IsClosedImmersion.of_comp_isClosedImmersion _ p
  refine { surj := ?_ }
  intro x
  obtain ⟨z, hz⟩ := T.hom.left.surjective (p x)
  refine ⟨z, p.isClosedEmbedding.injective ?_⟩
  change (comparisonPullbackHom T U i hi ≫ p) z = p x
  rw [show comparisonPullbackHom T U i hi ≫ p = T.hom.left from
    comparisonPullbackHom_snd T U i hi]
  exact hz

/-- The thickening of `Z` over `Y` whose ambient scheme is the canonical fibre product
`Y ×_[Y'] Z'`. -/
noncomputable def comparisonPullback : Thickening.Over U.left.left :=
  MorphismProperty.Arrow.mk
    (CategoryTheory.Over.homMk (comparisonPullbackHom T U i hi)
      (comparisonPullbackHom_fst T U i hi) :
        CategoryTheory.Over.mk i ⟶
          CategoryTheory.Over.mk
            (pullback.fst U.hom.left (ambientComparison T U i hi)))
    (comparisonPullbackHom_isThickening T U i hi)

/-- The closed part of the comparison pullback thickening is `Z ⟶ Y`. -/
theorem comparisonPullback_left :
    (comparisonPullback T U i hi).left = CategoryTheory.Over.mk i := rfl

/-- The ambient part of the comparison pullback thickening is
`Y ×_[Y'] Z' ⟶ Y`. -/
theorem comparisonPullback_right :
    (comparisonPullback T U i hi).right =
      CategoryTheory.Over.mk
        (pullback.fst U.hom.left (ambientComparison T U i hi)) := rfl

/-- The defining scheme morphism of the comparison pullback thickening is the canonical map
from `Z` to `Y ×_[Y'] Z'`. -/
theorem comparisonPullback_hom :
    (CategoryTheory.Over.forget U.left.left).map (comparisonPullback T U i hi).hom =
      comparisonPullbackHom T U i hi := rfl

/-- The ambient scheme of the comparison pullback is the chosen categorical pullback of
`Y ⟶ Y'` and `Z' ⟶ Y'`. -/
theorem comparisonPullback_isPullback :
    IsPullback
      (pullback.fst U.hom.left (ambientComparison T U i hi))
      (pullback.snd U.hom.left (ambientComparison T U i hi))
      U.hom.left (ambientComparison T U i hi) :=
  IsPullback.of_hasPullback _ _

set_option backward.isDefEq.respectTransparency false in
/-- A closed factor of a first-order thickening through a closed immersion is first order. -/
private theorem isFirstOrderThickening_of_comp_isClosedImmersion {Z P Z' : Scheme.{u}} (j : Z ⟶ P) (p : P ⟶ Z')
    [IsClosedImmersion j] [IsClosedImmersion p]
    [h : IsFirstOrderThickening (j ≫ p)] : IsFirstOrderThickening j := by
  have hpow : j.ker ^ 2 = 0 := by
    apply Scheme.IdealSheafData.ext_of_iSup_eq_top
      (fun V : Z'.affineOpens ↦ ⟨p ⁻¹ᵁ V, V.2.preimage p⟩)
      (p.iSup_preimage_eq_top (iSup_affineOpens_eq_top Z'))
    intro V
    change (j.ker.ideal ⟨p ⁻¹ᵁ V, V.2.preimage p⟩) ^ 2 = ⊥
    rw [Scheme.Hom.ker_apply]
    have hk : (RingHom.ker (j.app (p ⁻¹ᵁ V)).hom).comap (p.app V).hom =
        RingHom.ker ((j ≫ p).app V).hom := by
      rw [RingHom.comap_ker]
      rfl
    have hp : (RingHom.ker ((j ≫ p).app V).hom) ^ 2 = ⊥ := by
      have hv := congrArg (fun I : Z'.IdealSheafData ↦ I.ideal V) h.ker_pow_succ
      change ((j ≫ p).ker.ideal V) ^ 2 = ⊥ at hv
      rwa [Scheme.Hom.ker_apply] at hv
    rw [← Ideal.map_comap_of_surjective (p.app V).hom (p.app_surjective V V.2)
      (RingHom.ker (j.app (p ⁻¹ᵁ V)).hom), hk, ← Ideal.map_pow, hp, Ideal.map_bot]
  exact
    { isClosedImmersion := inferInstance
      ker_isNilpotent := ⟨2, hpow⟩
      ker_pow_succ := hpow }

set_option backward.isDefEq.respectTransparency false in
/-- If `Z ⟶ Y ⟶ X` is formally unramified, the comparison-pullback thickening induced by
chosen universal first-order thickenings of `Z` and `Y` over `X` is universal over `Y`. -/
instance comparisonPullback_isUniversal [FormallyUnramified i]
    [FormallyUnramified U.left.hom] :
    IsUniversalFirstOrder (comparisonPullback T U i hi) := by
  letI : IsThickening U.hom.left := U.prop
  let p := pullback.snd U.hom.left (ambientComparison T U i hi)
  have hU : U.hom.left ≫ U.right.hom = U.left.hom := CategoryTheory.Over.w U.hom
  have hp_over : p ≫ T.right.hom =
      pullback.fst U.hom.left (ambientComparison T U i hi) ≫ U.left.hom := by
    rw [← ambientComparison_over T U i hi, ← Category.assoc,
      ← pullback.condition, Category.assoc, hU]
  refine ⟨?_, ?_⟩
  · show IsFirstOrderThickening ((CategoryTheory.Over.forget U.left.left).map
      (comparisonPullback T U i hi).hom)
    letI : IsFirstOrderThickening (comparisonPullbackHom T U i hi ≫ p) :=
      (comparisonPullbackHom_snd T U i hi).symm ▸
        (IsUniversalFirstOrder.isFirstOrder (T := T))
    exact isFirstOrderThickening_of_comp_isClosedImmersion (comparisonPullbackHom T U i hi) p
  · intro V hV a
    -- Lift over X, then use universality of U to factor the ambient map through the pullback.
    have ha : a.left ≫ i = V.left.hom := CategoryTheory.Over.w a
    have hV_over : V.hom.left ≫ V.right.hom = V.left.hom := CategoryTheory.Over.w V.hom
    let V' := (Thickening.Over.map U.left.hom).obj V
    letI : IsFirstOrderThickening ((CategoryTheory.Over.forget X).map V'.hom) := hV
    let aX : V'.left ⟶ T.left := CategoryTheory.Over.homMk a.left (by
      change a.left ≫ T.left.hom = V.left.hom ≫ U.left.hom
      rw [← hi, ← Category.assoc, ha])
    obtain ⟨b, hb, hb_unique⟩ := existsUniqueLift V' aX
    have hb_left : b.left.left = a.left :=
      congrArg (fun f : V'.left ⟶ T.left ↦ f.left) hb
    have hb_comm : a.left ≫ T.hom.left = V.hom.left ≫ b.right.left := by
      have hw := congrArg (fun f : V'.left ⟶ T.right ↦ f.left)
        (MorphismProperty.Arrow.w b)
      change b.left.left ≫ T.hom.left = V.hom.left ≫ b.right.left at hw
      rw [hb_left] at hw
      exact hw
    let c : V' ⟶ U := MorphismProperty.Arrow.homMk
      (CategoryTheory.Over.homMk V.left.hom rfl)
      (CategoryTheory.Over.homMk (V.right.hom ≫ U.hom.left) (by
        change (V.right.hom ≫ U.hom.left) ≫ U.right.hom = V.right.hom ≫ U.left.hom
        rw [Category.assoc, hU]))
      (by
        apply CategoryTheory.Over.OverMorphism.ext
        change V.left.hom ≫ U.hom.left = V.hom.left ≫ (V.right.hom ≫ U.hom.left)
        rw [← Category.assoc, hV_over])
    let u : T ⟶ U := lift T (CategoryTheory.Over.homMk i hi)
    have hu_left : u.left.left = i :=
      congrArg (fun f : T.left ⟶ U.left ↦ f.left)
        (existsUniqueLift T (CategoryTheory.Over.homMk i hi)).choose_spec.1
    have hbc : (b ≫ u).left = c.left := by
      apply CategoryTheory.Over.OverMorphism.ext
      change b.left.left ≫ u.left.left = V.left.hom
      rw [hb_left, hu_left, ha]
    have hbc' : b ≫ u = c := (existsUniqueLift V' c.left).unique hbc rfl
    have hbU : b.right.left ≫ ambientComparison T U i hi = V.right.hom ≫ U.hom.left :=
      congrArg (fun f : V' ⟶ U ↦ f.right.left) hbc'
    let bY := pullback.lift V.right.hom b.right.left hbU.symm
    let k : V ⟶ comparisonPullback T U i hi := MorphismProperty.Arrow.homMk a
      (CategoryTheory.Over.homMk bY (pullback.lift_fst _ _ _)) (by
        apply CategoryTheory.Over.OverMorphism.ext
        apply pullback.hom_ext
        · show (a.left ≫ comparisonPullbackHom T U i hi) ≫
            pullback.fst U.hom.left (ambientComparison T U i hi) =
            (V.hom.left ≫ bY) ≫ pullback.fst U.hom.left (ambientComparison T U i hi)
          simp only [Category.assoc, comparisonPullbackHom_fst, bY, pullback.lift_fst]
          exact ha.trans hV_over.symm
        · show (a.left ≫ comparisonPullbackHom T U i hi) ≫ p = (V.hom.left ≫ bY) ≫ p
          simpa only [Category.assoc, p, comparisonPullbackHom_snd, bY, pullback.lift_snd]
            using hb_comm)
    refine ⟨k, rfl, ?_⟩
    intro l hl
    -- Project any other lift to T and use uniqueness over X.
    have hl_left : l.left.left = a.left := congrArg
      (fun f : V.left ⟶ (comparisonPullback T U i hi).left ↦ f.left) hl
    have hl_comm : l.left.left ≫ comparisonPullbackHom T U i hi =
        V.hom.left ≫ l.right.left :=
      congrArg (fun f : V.left ⟶ (comparisonPullback T U i hi).right ↦ f.left)
        (MorphismProperty.Arrow.w l)
    have hl_over : l.right.left ≫
        pullback.fst U.hom.left (ambientComparison T U i hi) = V.right.hom :=
      CategoryTheory.Over.w l.right
    let e : V' ⟶ T := MorphismProperty.Arrow.homMk aX
      (CategoryTheory.Over.homMk (l.right.left ≫ p) (by
        change (l.right.left ≫ p) ≫ T.right.hom = V.right.hom ≫ U.left.hom
        rw [Category.assoc, hp_over, ← Category.assoc, hl_over]))
      (by
        apply CategoryTheory.Over.OverMorphism.ext
        change a.left ≫ T.hom.left = V.hom.left ≫ (l.right.left ≫ p)
        have hw := congrArg (fun f : V.left.left ⟶
          pullback U.hom.left (ambientComparison T U i hi) ↦ f ≫ p) hl_comm
        simpa only [Category.assoc, p, comparisonPullbackHom_snd, hl_left] using hw)
    have he : e = b := hb_unique e rfl
    apply MorphismProperty.Arrow.Hom.ext hl
    apply CategoryTheory.Over.OverMorphism.ext
    apply pullback.hom_ext
    · change l.right.left ≫ pullback.fst U.hom.left (ambientComparison T U i hi) =
        bY ≫ pullback.fst U.hom.left (ambientComparison T U i hi)
      rw [hl_over, pullback.lift_fst]
    · change l.right.left ≫ p = bY ≫ p
      rw [show bY ≫ p = b.right.left from pullback.lift_snd _ _ _]
      exact congrArg (fun f : V' ⟶ T ↦ f.right.left) he

end AlgebraicGeometry.Thickening.IsUniversalFirstOrder
