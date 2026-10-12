/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CatCommSqOver

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Pushout

/-- The square of restricted base-change functors associated to a pushout span. -/
noncomputable def baseChangeSquare (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] {Z X Y : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    [HasPushout i j] :
    CategoricalPullback.CatCommSqOver
      (MorphismProperty.Over.pullback P ⊤ i)
      (MorphismProperty.Over.pullback P ⊤ j) (P.Over ⊤ (pushout i j)) where
  fst := MorphismProperty.Over.pullback P ⊤ (pushout.inl i j)
  snd := MorphismProperty.Over.pullback P ⊤ (pushout.inr i j)
  iso := (MorphismProperty.Over.pullbackComp i (pushout.inl i j)).symm ≪≫
    MorphismProperty.Over.pullbackCongr
      (pushout.condition : i ≫ pushout.inl i j = j ≫ pushout.inr i j) ≪≫
    MorphismProperty.Over.pullbackComp j (pushout.inr i j)

/-- The first leg of `baseChangeSquare P i j` is restriction to `X`. -/
theorem baseChangeSquare_fst (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] {Z X Y : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    [HasPushout i j] :
    (baseChangeSquare P i j).fst =
      MorphismProperty.Over.pullback P ⊤ (pushout.inl i j) := sorry

/-- The second leg of `baseChangeSquare P i j` is restriction to `Y`. -/
theorem baseChangeSquare_snd (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] {Z X Y : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    [HasPushout i j] :
    (baseChangeSquare P i j).snd =
      MorphismProperty.Over.pullback P ⊤ (pushout.inr i j) := sorry

/-- Restriction from objects over a pushout to compatible objects over its two components. -/
noncomputable def baseChange (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] {Z X Y : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    [HasPushout i j] :
    P.Over ⊤ (pushout i j) ⥤
      CategoricalPullback (MorphismProperty.Over.pullback P ⊤ i)
        (MorphismProperty.Over.pullback P ⊤ j) :=
  (baseChangeSquare P i j).comparison

/-- The first component of `baseChange P i j` is restriction along the first coprojection. -/
theorem baseChange_obj_fst (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] {Z X Y : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    [HasPushout i j] (W : P.Over ⊤ (pushout i j)) :
    ((baseChange P i j).obj W).fst =
      (MorphismProperty.Over.pullback P ⊤ (pushout.inl i j)).obj W := sorry

/-- The second component of `baseChange P i j` is restriction along the second coprojection. -/
theorem baseChange_obj_snd (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] {Z X Y : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    [HasPushout i j] (W : P.Over ⊤ (pushout i j)) :
    ((baseChange P i j).obj W).snd =
      (MorphismProperty.Over.pullback P ⊤ (pushout.inr i j)).obj W := sorry

/-- The overlap isomorphism of `baseChange P i j` is the canonical comparison from its
base-change square. -/
theorem baseChange_obj_iso (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] {Z X Y : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    [HasPushout i j] (W : P.Over ⊤ (pushout i j)) :
    ((baseChange P i j).obj W).iso = (baseChangeSquare P i j).iso.app W := sorry

end AlgebraicGeometry.Scheme.Pushout
