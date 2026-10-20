/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.ComponentRestriction
public import ReasLib.AlgebraicGeometry.ChowGroup.FlatPullback.Identity

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass.ComponentRestriction

private theorem grading_cast_heq {M : ℤ → Type*} [∀ n, AddCommGroup (M n)]
    {a b : ℤ} (h : a = b) (x : M a) : HEq (AddEquiv.cast h x) x := by
  subst b
  rfl

/-- A component cap agrees with the ambient cap whenever its test square is also
cartesian over the ambient morphism. -/
theorem restrict_cap_of_isPullback
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) (U : X.left.Opens) (V : Y.left.Opens)
    (h : U ≤ f.left ⁻¹ᵁ V) (c : BivariantClass δ f p)
    {X' Y' : Over S} [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (i : X' ⟶ over X U) (f' : X' ⟶ Y') (g : Y' ⟶ over Y V)
    [LocallyOfFiniteType g.left] [LocallyOfFiniteType (g ≫ ι Y V).left]
    (square : IsPullback i.left f'.left (hom f U V h).left g.left)
    (ambient : IsPullback (i ≫ ι X U).left f'.left f.left (g ≫ ι Y V).left)
    (k : ℤ) :
    (restrict δ f p U V h c).cap i f' g square k =
      c.cap (i ≫ ι X U) f' (g ≫ ι Y V) ambient k := by
  -- Local instance justification (proof-local temporary data): ambient cap evaluation requires finite type of the canonical base-change object, derived from its structure morphisms.
  letI : LocallyOfFiniteType (baseChange f (g ≫ ι Y V)).hom :=
    locallyOfFiniteTypeBaseChange f (g ≫ ι Y V)
  -- Local instance justification (proof-local temporary data): flat-pullback compatibility requires the proved flatness of this component comparison map.
  letI : Flat (componentLift f U V h i f' g square).left :=
    flatComponentLift f U V h i f' g square
  -- Local instance justification (proof-local temporary data): flat-pullback compatibility requires the proved relative dimension zero of this component comparison map.
  letI : Scheme.Hom.RelativeDimension (componentLift f U V h i f' g square).left 0 :=
    relativeDimensionComponentLift f U V h i f' g square
  -- Local instance justification (proof-local temporary data): the identity base-change comparison requires relative dimension zero for the underlying over-category identity.
  letI : Scheme.Hom.RelativeDimension (𝟙 Y' : Y' ⟶ Y').left 0 := by
    rw [Over.id_left]
    infer_instance
  have hs : componentLift f U V h i f' g square ≫
      baseChangeToSource f (g ≫ ι Y V) = i ≫ ι X U := by
    apply Over.OverMorphism.ext
    change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
    exact pullback.lift_snd _ _ _
  have ht : (componentLift f U V h i f' g square).left ≫
      (baseChangeToTarget f (g ≫ ι Y V)).left = f'.left ≫ (𝟙 Y' : Y' ⟶ Y').left := by
    rw [Over.id_left, Category.comp_id]
    change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
    exact pullback.lift_fst _ _ _
  have inner : IsPullback (componentLift f U V h i f' g square).left f'.left
      (baseChangeToTarget f (g ≫ ι Y V)).left (𝟙 Y' : Y' ⟶ Y').left := by
    apply IsPullback.of_right _ ht (baseChange_isPullback f (g ≫ ι Y V))
    simpa only [← Over.comp_left, hs, Category.id_comp] using ambient
  apply AddMonoidHom.ext
  intro α
  have compat := c.pullback_flat
    (baseChangeToSource f (g ≫ ι Y V)) (baseChangeToTarget f (g ≫ ι Y V))
    (g ≫ ι Y V) (baseChange_isPullback f (g ≫ ι Y V))
    (componentLift f U V h i f' g square) f' (𝟙 Y') inner 0 k α
  have hid := congrArg (fun q : RelativeChow δ Y' k →+ RelativeChow δ Y' k ↦ q α)
    (ChowGroup.flatPullback_id δ Y' k)
  have input : HEq (ChowGroup.flatPullback δ Y' Y' (𝟙 Y') 0 k α) α :=
    (grading_cast_heq (add_zero k) _).symm.trans (heq_of_eq hid)
  have capInput : HEq
      (c.cap (componentLift f U V h i f' g square ≫ baseChangeToSource f (g ≫ ι Y V))
        f' ((𝟙 Y') ≫ (g ≫ ι Y V)) (inner.paste_horiz (baseChange_isPullback f (g ≫ ι Y V)))
        (k + (0 : ℕ)) (ChowGroup.flatPullback δ Y' Y' (𝟙 Y') 0 k α))
      (c.cap (i ≫ ι X U) f' (g ≫ ι Y V) ambient k α) := by
    simp only [hs, Category.id_comp]
    have graded (a b : ℤ) (hab : a = b) (x : RelativeChow δ Y' a)
        (y : RelativeChow δ Y' b) (hxy : HEq x y) :
        HEq (c.cap (i ≫ ι X U) f' (g ≫ ι Y V) ambient a x)
          (c.cap (i ≫ ι X U) f' (g ≫ ι Y V) ambient b y) := by
      subst b
      cases hxy
      rfl
    exact graded _ _ (by simp) _ _ input
  apply eq_of_heq
  exact (grading_cast_heq (componentDegree k p) _).trans (compat.symm.trans capInput)

end AlgebraicGeometry.BivariantClass.ComponentRestriction
