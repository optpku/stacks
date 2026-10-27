/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening

/-!
# Restrictions of thickenings to open subschemes

A thickening transports opens of its closed part to opens of its ambient scheme. Compatible
opens over a base scheme determine a restricted bundled thickening, and the resulting square
with the two open immersions is cartesian.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry

/-- Restricting a first-order thickening over an open of its target is again a first-order
thickening. -/
instance morphismRestrict_isFirstOrderThickening {X X' : Scheme.{u}} (i : X ⟶ X')
    [IsFirstOrderThickening i] (U' : X'.Opens) :
    IsFirstOrderThickening (i ∣_ U') := by
  letI : IsClosedImmersion i := IsFiniteOrderThickening.isClosedImmersion
  have hker : (i ∣_ U').ker ^ 2 = 0 := by
    apply Scheme.IdealSheafData.ext
    funext W
    change (i ∣_ U').ker.ideal W ^ 2 = ⊥
    rw [Scheme.ker_morphismRestrict_ideal]
    exact congrArg
      (fun I : X'.IdealSheafData =>
        I.ideal ⟨U'.ι ''ᵁ W, W.2.image_of_isOpenImmersion _⟩)
      (IsNthOrderThickening.ker_pow_succ (n := 1) (i := i))
  exact
    { isClosedImmersion := inferInstance
      ker_isNilpotent := ⟨2, hker⟩
      ker_pow_succ := hker }

/-- Restriction of a morphism over `S` to an open of its target is again a morphism over `S`. -/
instance morphismRestrict_isOver {X X' : Scheme.{u}} (S : Scheme.{u}) (i : X ⟶ X')
    [X.Over S] [X'.Over S] [i.IsOver S] (U' : X'.Opens) :
    (i ∣_ U').IsOver S := by
  constructor
  change (i ∣_ U') ≫ U'.ι ≫ X' ↘ S = (i ⁻¹ᵁ U').ι ≫ X ↘ S
  rw [morphismRestrict_ι_assoc, comp_over]

namespace Thickening.Over

/-- The defining morphism of a bundled thickening over a scheme is a thickening. -/
instance instIsThickeningHom {X : Scheme.{u}} (T : Thickening.Over X) :
    IsThickening T.hom.left :=
  T.prop

end Thickening.Over

namespace IsThickening

/-- The order equivalence on open subschemes induced by the homeomorphism underlying a
thickening. -/
noncomputable def opensEquiv {Z Z' : Scheme.{u}} (i : Z ⟶ Z') [IsThickening i] :
    Z.Opens ≃o Z'.Opens :=
  (i.isClosedEmbedding.toHomeomorphOfSurjective i.surjective).opensCongr

/-- Pulling back the open transported along a thickening recovers the original open. -/
theorem preimage_opensEquiv {Z Z' : Scheme.{u}} (i : Z ⟶ Z') [IsThickening i]
    (V : Z.Opens) :
    i ⁻¹ᵁ (opensEquiv i V) = V := by
  exact (i.isClosedEmbedding.toHomeomorphOfSurjective i.surjective).opensCongr.symm_apply_apply V

end IsThickening

namespace Thickening.Over

set_option backward.isDefEq.respectTransparency false in
/-- The ambient open corresponding to a compatible open in the closed part remains over the
chosen open in the base. -/
theorem ambientOpen_le {X : Scheme.{u}} (T : Thickening.Over X)
    (U : X.Opens) (V : T.left.left.Opens) (hV : V ≤ T.left.hom ⁻¹ᵁ U) :
    IsThickening.opensEquiv T.hom.left V ≤ T.right.hom ⁻¹ᵁ U := by
  intro x' hx'
  obtain ⟨x, rfl⟩ := T.hom.left.surjective x'
  have hx : x ∈ V := by
    rw [← IsThickening.preimage_opensEquiv T.hom.left V]
    exact hx'
  change (T.hom.left ≫ T.right.hom) x ∈ U
  have hw : T.hom.left ≫ T.right.hom = T.left.hom := Over.w T.hom
  rw [hw]
  exact hV hx

set_option backward.isDefEq.respectTransparency false in
/-- Restricting the defining morphism of a thickening to corresponding opens is again a
thickening. -/
instance restrictHom_isThickening {X : Scheme.{u}} (T : Thickening.Over X)
    (V : T.left.left.Opens) :
    IsThickening
      (T.hom.left.resLE (IsThickening.opensEquiv T.hom.left V) V
        (le_of_eq (IsThickening.preimage_opensEquiv T.hom.left V).symm)) := by
  have H : IsPullback
      (T.hom.left.resLE (IsThickening.opensEquiv T.hom.left V) V
        (le_of_eq (IsThickening.preimage_opensEquiv T.hom.left V).symm))
      V.ι (IsThickening.opensEquiv T.hom.left V).ι T.hom.left :=
    IsOpenImmersion.isPullback _ _ _ _ (by simp)
      (by simpa using IsThickening.preimage_opensEquiv T.hom.left V)
  refine
    { toIsClosedImmersion := MorphismProperty.of_isPullback H.flip
        (show IsClosedImmersion T.hom.left from inferInstance)
      toSurjective := ⟨?_⟩ }
  intro y
  obtain ⟨x, hx⟩ := T.hom.left.surjective y.1
  have hxV : x ∈ V := by
    rw [← IsThickening.preimage_opensEquiv T.hom.left V]
    change T.hom.left x ∈ IsThickening.opensEquiv T.hom.left V
    rw [hx]
    exact y.2
  refine ⟨⟨x, hxV⟩, ?_⟩
  apply Subtype.ext
  simpa only [Scheme.Hom.coe_resLE_apply] using hx

/-- The restrictions of the closed and ambient structural maps commute with the restricted
defining morphism. -/
theorem restrictHom_over {X : Scheme.{u}} (T : Thickening.Over X)
    (U : X.Opens) (V : T.left.left.Opens) (hV : V ≤ T.left.hom ⁻¹ᵁ U) :
    T.hom.left.resLE (IsThickening.opensEquiv T.hom.left V) V
        (le_of_eq (IsThickening.preimage_opensEquiv T.hom.left V).symm) ≫
      T.right.hom.resLE U (IsThickening.opensEquiv T.hom.left V)
        (ambientOpen_le T U V hV) =
    T.left.hom.resLE U V hV := by
  apply (cancel_mono U.ι).mp
  simp

/-- Restrict a bundled thickening over `X` to compatible opens in its closed part and in
`X`. -/
noncomputable def restrict {X : Scheme.{u}} (T : Thickening.Over X)
    (U : X.Opens) (V : T.left.left.Opens) (hV : V ≤ T.left.hom ⁻¹ᵁ U) :
    Thickening.Over U :=
  MorphismProperty.Arrow.mk
    (Over.homMk
      (T.hom.left.resLE (IsThickening.opensEquiv T.hom.left V) V
        (le_of_eq (IsThickening.preimage_opensEquiv T.hom.left V).symm))
      (restrictHom_over T U V hV) :
      Over.mk (T.left.hom.resLE U V hV) ⟶
        Over.mk (T.right.hom.resLE U (IsThickening.opensEquiv T.hom.left V)
          (ambientOpen_le T U V hV)))
    (restrictHom_isThickening T V)

/-- The closed part of a restricted thickening is the prescribed open over the restricted
base. -/
theorem restrict_left {X : Scheme.{u}} (T : Thickening.Over X)
    (U : X.Opens) (V : T.left.left.Opens) (hV : V ≤ T.left.hom ⁻¹ᵁ U) :
    (restrict T U V hV).left = Over.mk (T.left.hom.resLE U V hV) := by
  rfl

/-- The ambient part of a restricted thickening is the corresponding transported open over
the restricted base. -/
theorem restrict_right {X : Scheme.{u}} (T : Thickening.Over X)
    (U : X.Opens) (V : T.left.left.Opens) (hV : V ≤ T.left.hom ⁻¹ᵁ U) :
    (restrict T U V hV).right =
      Over.mk (T.right.hom.resLE U (IsThickening.opensEquiv T.hom.left V)
        (ambientOpen_le T U V hV)) := by
  rfl

/-- The defining morphism of a restricted thickening is the restriction of the original
defining morphism to the corresponding opens. -/
theorem restrict_hom {X : Scheme.{u}} (T : Thickening.Over X)
    (U : X.Opens) (V : T.left.left.Opens) (hV : V ≤ T.left.hom ⁻¹ᵁ U) :
    (restrict T U V hV).hom.left =
      T.hom.left.resLE (IsThickening.opensEquiv T.hom.left V) V
        (le_of_eq (IsThickening.preimage_opensEquiv T.hom.left V).symm) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The defining morphism of a restricted thickening forms a pullback square with the two
open immersions. -/
theorem restrictSquare {X : Scheme.{u}} (T : Thickening.Over X)
    (U : X.Opens) (V : T.left.left.Opens) (hV : V ≤ T.left.hom ⁻¹ᵁ U) :
    IsPullback V.ι (restrict T U V hV).hom.left T.hom.left
      (IsThickening.opensEquiv T.hom.left V).ι := by
  exact (IsOpenImmersion.isPullback _ _ _ _ (by simp [restrict_hom])
    (by simpa using IsThickening.preimage_opensEquiv T.hom.left V)).flip

end Thickening.Over

end AlgebraicGeometry
