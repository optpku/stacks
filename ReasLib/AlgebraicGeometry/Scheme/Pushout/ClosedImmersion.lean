/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Pushout.AdmissibleSpan.Existence

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Pushout.ClosedImmersion

/-- Two closed immersions, regarded as morphisms over the terminal scheme, form an
admissible span. -/
instance instIsAdmissibleSpan {Z X Y : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    Scheme.Pushout.IsAdmissibleSpan
      (i.asOver (⊤_ Scheme)) (j.asOver (⊤_ Scheme)) := sorry

/-- Two closed immersions of schemes have a canonical pushout. -/
instance instHasPushout {Z X Y : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] : HasPushout i j := sorry

/-- The canonical pushout square of two closed immersions is a pullback square. -/
theorem isPullback {Z X Y : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    IsPullback i j (pushout.inl i j) (pushout.inr i j) := sorry

/-- The first coprojection into the pushout of two closed immersions is a closed
immersion. -/
instance instInlIsClosedImmersion {Z X Y : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    IsClosedImmersion (pushout.inl i j) := sorry

/-- The second coprojection into the pushout of two closed immersions is a closed
immersion. -/
instance instInrIsClosedImmersion {Z X Y : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    IsClosedImmersion (pushout.inr i j) := sorry

/-- The common morphism from the source of two closed immersions to their pushout. -/
noncomputable def common {Z X Y : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] : Z ⟶ pushout i j :=
  i ≫ pushout.inl i j

/-- The common morphism is also the second closed immersion followed by the second
coprojection. -/
theorem common_eq {Z X Y : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    common i j = j ≫ pushout.inr i j := sorry

/-- The structure sheaf on the pushout of two closed immersions is the sectionwise
pullback of the three pushed-forward structure sheaves. -/
theorem structureSheaf_isPullback {Z X Y : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    IsStructureSheafPullback (IsPushout.of_hasPushout i j).toCommSq := sorry

end AlgebraicGeometry.Scheme.Pushout.ClosedImmersion
