/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.UniversalFirstOrder.Functorial

/-!
# Comparison pullbacks of universal first-order thickenings of algebraic spaces

Chosen universal first-order thickenings of `Z` and `Y` over `X` determine a
canonical comparison `Z' ⟶ Y'`. The fibre product `Y ×_{Y'} Z'`
carries a closed immersion of `Z` which is a universal first-order thickening
of `Z` over `Y`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder

variable {S : Scheme.{u}} {X Y Z Z' Y' : AlgebraicSpace S}
variable (iZ : Z ⟶ Z') (fZ : Z' ⟶ X) (iY : Y ⟶ Y') (fY : Y' ⟶ X)
variable (i : Z ⟶ Y)
variable [IsUniversalFirstOrder iZ fZ] [IsUniversalFirstOrder iY fY]
variable [FormallyUnramified (iZ ≫ fZ)] [FormallyUnramified (iY ≫ fY)]
variable (sq : CommSq i (iZ ≫ fZ) (iY ≫ fY) (𝟙 X))

/-- The fibre product `Y ×_{Y'} Z'` of the closed immersion `Y ⊂ Y'` with the
canonical comparison morphism `Z' ⟶ Y'`. -/
noncomputable def comparisonPullback : AlgebraicSpace S :=
  pullback iY (comparison iZ fZ iY fY i (𝟙 X) sq)

/-- `comparisonPullback` is the chosen categorical fibre product of `Y ⟶ Y'` and
the comparison `Z' ⟶ Y'`. -/
theorem comparisonPullback_eq :
    comparisonPullback iZ fZ iY fY i sq =
      pullback iY (comparison iZ fZ iY fY i (𝟙 X) sq) :=
  rfl

/-- The canonical closed immersion of `Z` into the fibre product `Y ×_{Y'} Z'`. -/
noncomputable def comparisonPullbackHom : Z ⟶ comparisonPullback iZ fZ iY fY i sq :=
  pullback.lift i iZ (comparison_comp iZ fZ iY fY i (𝟙 X) sq)

/-- `comparisonPullbackHom` is the mediating map of `i : Z ⟶ Y` and `Z ⊂ Z'` into
the fibre product. -/
theorem comparisonPullbackHom_eq :
    comparisonPullbackHom iZ fZ iY fY i sq =
      pullback.lift i iZ (comparison_comp iZ fZ iY fY i (𝟙 X) sq) :=
  rfl

/-- The first projection of `comparisonPullbackHom` recovers `i : Z ⟶ Y`. -/
theorem comparisonPullbackHom_fst :
    comparisonPullbackHom iZ fZ iY fY i sq ≫
        pullback.fst iY (comparison iZ fZ iY fY i (𝟙 X) sq) =
      i :=
  pullback.lift_fst _ _ _

/-- The second projection of `comparisonPullbackHom` recovers `Z ⊂ Z'`. -/
theorem comparisonPullbackHom_snd :
    comparisonPullbackHom iZ fZ iY fY i sq ≫
        pullback.snd iY (comparison iZ fZ iY fY i (𝟙 X) sq) =
      iZ :=
  pullback.lift_snd _ _ _

/-- The canonical map `Z ⟶ Y ×_{Y'} Z'` is a first-order thickening. -/
instance comparisonPullbackHom_isFirstOrderThickening :
    IsFirstOrderThickening (comparisonPullbackHom iZ fZ iY fY i sq) :=
  sorry

/-- The structure morphism of the comparison-pullback thickening over `Y` is
formally unramified when `Z ⟶ Y` is. -/
instance comparisonPullbackHom_fst_formallyUnramified [FormallyUnramified i] :
    FormallyUnramified
      (comparisonPullbackHom iZ fZ iY fY i sq ≫
        pullback.fst iY (comparison iZ fZ iY fY i (𝟙 X) sq)) :=
  by
    rw [comparisonPullbackHom_fst]
    infer_instance

/-- If `Z ⟶ Y` is formally unramified, the comparison-pullback thickening
`Z ⊂ Y ×_{Y'} Z'` is a universal first-order thickening of `Z` over `Y`. -/
instance comparisonPullback_isUniversal [FormallyUnramified i] :
    IsUniversalFirstOrder (comparisonPullbackHom iZ fZ iY fY i sq)
      (pullback.fst iY (comparison iZ fZ iY fY i (𝟙 X) sq)) :=
  by
    refine { toIsFirstOrderThickening := inferInstance, existsUniqueLift := ?_ }
    intro T T' j b hj a h_solid
    have h_over : a ≫ i = j ≫ b := by
      simpa only [comparisonPullbackHom_fst] using h_solid
    have h_sq : i ≫ iY ≫ fY = iZ ≫ fZ :=
      sq.w.trans (Category.comp_id _)
    obtain ⟨a', ⟨ha'_closed, ha'_over⟩, ha'_unique⟩ :=
      existsUniqueLift (i := iZ) (f := fZ) j (b ≫ iY ≫ fY) a
        (by simpa only [Category.assoc (obj := AlgebraicSpace S), h_sq] using
          congrArg (fun k ↦ k ≫ iY ≫ fY) h_over)
    have h_compare : b ≫ iY = a' ≫ comparison iZ fZ iY fY i (𝟙 X) sq := by
      apply (existsUniqueLift (i := iY) (f := fY) j (b ≫ iY ≫ fY) (a ≫ i)
        (by simpa only [Category.assoc (obj := AlgebraicSpace S)] using
          congrArg (fun k ↦ k ≫ iY ≫ fY) h_over)).unique
      · exact ⟨by simpa only [Category.assoc (obj := AlgebraicSpace S)] using
          congrArg (fun k ↦ k ≫ iY) h_over,
          Category.assoc (obj := AlgebraicSpace S) _ _ _⟩
      · constructor
        · calc
            (a ≫ i) ≫ iY = a ≫ iZ ≫ comparison iZ fZ iY fY i (𝟙 X) sq := by
              rw [Category.assoc (obj := AlgebraicSpace S),
                comparison_comp iZ fZ iY fY i (𝟙 X) sq]
            _ = j ≫ (a' ≫ comparison iZ fZ iY fY i (𝟙 X) sq) := by
              rw [← Category.assoc (obj := AlgebraicSpace S), ha'_closed,
                Category.assoc (obj := AlgebraicSpace S)]
        · simp only [Category.assoc (obj := AlgebraicSpace S),
            comparison_over iZ fZ iY fY i (𝟙 X) sq, Category.comp_id, ha'_over]
    refine ⟨pullback.lift b a' h_compare, ⟨?_, pullback.lift_fst _ _ _⟩, ?_⟩
    · apply pullback.hom_ext (C := AlgebraicSpace S)
      · calc
          (a ≫ comparisonPullbackHom iZ fZ iY fY i sq) ≫
              pullback.fst iY (comparison iZ fZ iY fY i (𝟙 X) sq) = a ≫ i := by
            rw [Category.assoc (obj := AlgebraicSpace S), comparisonPullbackHom_fst]
          _ = j ≫ b := h_over
          _ = (j ≫ pullback.lift b a' h_compare) ≫
              pullback.fst iY (comparison iZ fZ iY fY i (𝟙 X) sq) := by
            rw [Category.assoc (obj := AlgebraicSpace S), pullback.lift_fst]
      · calc
          (a ≫ comparisonPullbackHom iZ fZ iY fY i sq) ≫
              pullback.snd iY (comparison iZ fZ iY fY i (𝟙 X) sq) = a ≫ iZ := by
            rw [Category.assoc (obj := AlgebraicSpace S), comparisonPullbackHom_snd]
          _ = j ≫ a' := ha'_closed
          _ = (j ≫ pullback.lift b a' h_compare) ≫
              pullback.snd iY (comparison iZ fZ iY fY i (𝟙 X) sq) := by
            rw [Category.assoc (obj := AlgebraicSpace S), pullback.lift_snd]
    · intro k hk
      apply pullback.hom_ext (C := AlgebraicSpace S)
      · exact hk.2.trans (pullback.lift_fst _ _ _).symm
      · rw [pullback.lift_snd]
        apply ha'_unique
        constructor
        · calc
            a ≫ iZ = a ≫ (comparisonPullbackHom iZ fZ iY fY i sq ≫
                pullback.snd iY (comparison iZ fZ iY fY i (𝟙 X) sq)) := by
              rw [comparisonPullbackHom_snd]
            _ = (a ≫ comparisonPullbackHom iZ fZ iY fY i sq) ≫
                pullback.snd iY (comparison iZ fZ iY fY i (𝟙 X) sq) :=
              (Category.assoc (obj := AlgebraicSpace S) _ _ _).symm
            _ = (j ≫ k) ≫
                pullback.snd iY (comparison iZ fZ iY fY i (𝟙 X) sq) :=
              congrArg (fun t ↦ t ≫
                pullback.snd iY (comparison iZ fZ iY fY i (𝟙 X) sq)) hk.1
            _ = j ≫ (k ≫
                pullback.snd iY (comparison iZ fZ iY fY i (𝟙 X) sq)) :=
              Category.assoc (obj := AlgebraicSpace S) _ _ _
        · have h_pb :
              pullback.fst iY (comparison iZ fZ iY fY i (𝟙 X) sq) ≫ iY ≫ fY =
                pullback.snd iY (comparison iZ fZ iY fY i (𝟙 X) sq) ≫ fZ := by
            rw [← Category.assoc (obj := AlgebraicSpace S), pullback.condition,
              Category.assoc (obj := AlgebraicSpace S),
              comparison_over iZ fZ iY fY i (𝟙 X) sq, Category.comp_id]
          calc
            (k ≫ pullback.snd iY (comparison iZ fZ iY fY i (𝟙 X) sq)) ≫ fZ =
                k ≫ (pullback.snd iY (comparison iZ fZ iY fY i (𝟙 X) sq) ≫ fZ) :=
              Category.assoc (obj := AlgebraicSpace S) _ _ _
            _ = k ≫ (pullback.fst iY (comparison iZ fZ iY fY i (𝟙 X) sq) ≫ iY ≫ fY) :=
              congrArg (fun t ↦ k ≫ t) h_pb.symm
            _ = (k ≫ pullback.fst iY (comparison iZ fZ iY fY i (𝟙 X) sq)) ≫
                iY ≫ fY :=
              (Category.assoc (obj := AlgebraicSpace S) _ _ _).symm
            _ = b ≫ iY ≫ fY := congrArg (fun t ↦ t ≫ iY ≫ fY) hk.2

end AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder
