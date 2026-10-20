/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Pushout.ClosedImmersion

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Pushout.ClosedImmersion

variable {Z X Y : Scheme.{u}}

/-- The projection from the pullback of `P.fst.hom` along `i` to `P.snd.left`,
transported through the chosen isomorphism in `P`. -/
def rightLeg (i : Z ⟶ X) (j : Z ⟶ Y)
    (P : CategoricalPullback (Over.pullback i) (Over.pullback j)) :
    pullback P.fst.hom i ⟶ P.snd.left :=
  P.iso.hom.left ≫ pullback.fst P.snd.hom j

/-- The transported right leg is the chosen overlap isomorphism followed by the
second pullback projection. -/
theorem rightLeg_def (i : Z ⟶ X) (j : Z ⟶ Y)
    (P : CategoricalPullback (Over.pullback i) (Over.pullback j)) :
    rightLeg i j P = P.iso.hom.left ≫ pullback.fst P.snd.hom j := sorry

/-- The transported right leg commutes with the maps to `Z` and `Y`. -/
theorem rightLeg_condition (i : Z ⟶ X) (j : Z ⟶ Y)
    (P : CategoricalPullback (Over.pullback i) (Over.pullback j)) :
    rightLeg i j P ≫ P.snd.hom = pullback.snd P.fst.hom i ≫ j := sorry

/-- The transported right leg of a closed immersion is a closed immersion. -/
instance rightLegIsClosedImmersion (i : Z ⟶ X) (j : Z ⟶ Y)
    [IsClosedImmersion j]
    (P : CategoricalPullback (Over.pullback i) (Over.pullback j)) :
    IsClosedImmersion (rightLeg i j P) := sorry

/-- The morphism between pushouts induced by a compatible pair of scheme
morphisms and its chosen isomorphism over `Z`. -/
def inducedMap (i : Z ⟶ X) (j : Z ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (P : CategoricalPullback (Over.pullback i) (Over.pullback j)) :
    pushout (pullback.fst P.fst.hom i) (rightLeg i j P) ⟶ pushout i j :=
  pushout.map (pullback.fst P.fst.hom i) (rightLeg i j P) i j
    P.fst.hom P.snd.hom (pullback.snd P.fst.hom i)
    pullback.condition (rightLeg_condition i j P)

/-- The induced morphism restricts to `P.fst.hom` on the first component. -/
theorem inducedMap_inl (i : Z ⟶ X) (j : Z ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (P : CategoricalPullback (Over.pullback i) (Over.pullback j)) :
    pushout.inl (pullback.fst P.fst.hom i) (rightLeg i j P) ≫ inducedMap i j P =
      P.fst.hom ≫ pushout.inl i j := sorry

/-- The induced morphism restricts to `P.snd.hom` on the second component. -/
theorem inducedMap_inr (i : Z ⟶ X) (j : Z ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (P : CategoricalPullback (Over.pullback i) (Over.pullback j)) :
    pushout.inr (pullback.fst P.fst.hom i) (rightLeg i j P) ≫ inducedMap i j P =
      P.snd.hom ≫ pushout.inr i j := sorry

end AlgebraicGeometry.Scheme.Pushout.ClosedImmersion
