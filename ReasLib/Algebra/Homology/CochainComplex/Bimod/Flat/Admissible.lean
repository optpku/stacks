/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Bimod.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fixed-base goodness and admissible short exact sequences

The two fixed-base goodness conditions satisfy all three two-out-of-three implications for short
exact sequences which split after forgetting the differential but retain the coefficient action.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory.Bimod

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Exactness passes to a retract in the functor category: the universal maps for each
finite limit and colimit restrict along the retraction. -/
private theorem exactFunctor_of_retraction
    {D E : Type*} [Category D] [Category E] {F G : D ⥤ E}
    (i : F ⟶ G) (r : G ⟶ F) (hi : i ≫ r = 𝟙 F)
    (hG : exactFunctor D E G) : exactFunctor D E F := by
  have hir (X : D) : i.app X ≫ r.app X = 𝟙 (F.obj X) :=
    NatTrans.congr_app hi X
  letI : PreservesFiniteLimits G := hG.1
  letI : PreservesFiniteColimits G := hG.2
  constructor
  · refine ⟨fun J _ _ ↦ ⟨fun {K} ↦ ⟨fun {c} hc ↦ ?_⟩⟩⟩
    let h := isLimitOfPreserves G hc
    refine ⟨{ lift := fun s ↦ ?_, fac := ?_, uniq := ?_ }⟩
    · change s.pt ⟶ F.obj c.pt
      let s' : Cone (K ⋙ G) := (Cone.postcompose (Functor.whiskerLeft K i)).obj s
      exact h.lift s' ≫ r.app c.pt
    · intro s j
      let s' : Cone (K ⋙ G) := (Cone.postcompose (Functor.whiskerLeft K i)).obj s
      simp only [Functor.mapCone_pt, Functor.mapCone_π_app]
      change (h.lift s' ≫ r.app c.pt) ≫ F.map (c.π.app j) = s.π.app j
      erw [Category.assoc, ← r.naturality, ← Category.assoc]
      erw [h.fac]
      change (s.π.app j ≫ i.app (K.obj j)) ≫ r.app (K.obj j) = s.π.app j
      erw [Category.assoc, hir, Category.comp_id]
    · intro s m hm
      let s' : Cone (K ⋙ G) := (Cone.postcompose (Functor.whiskerLeft K i)).obj s
      simp only [Functor.mapCone_pt, Functor.mapCone_π_app] at hm ⊢
      change s.pt ⟶ F.obj c.pt at m
      have hm' : m ≫ i.app c.pt = h.lift s' := by
        apply h.hom_ext
        intro j
        change (m ≫ i.app c.pt) ≫ G.map (c.π.app j) = _
        erw [Category.assoc, ← i.naturality, ← Category.assoc, hm, h.fac]
        rfl
      change m = h.lift s' ≫ r.app c.pt
      erw [← hm', Category.assoc, hir, Category.comp_id]
  · refine ⟨fun J _ _ ↦ ⟨fun {K} ↦ ⟨fun {c} hc ↦ ?_⟩⟩⟩
    let h := isColimitOfPreserves G hc
    refine ⟨{ desc := fun s ↦ ?_, fac := ?_, uniq := ?_ }⟩
    · change F.obj c.pt ⟶ s.pt
      let s' : Cocone (K ⋙ G) := (Cocone.precompose (Functor.whiskerLeft K r)).obj s
      exact i.app c.pt ≫ h.desc s'
    · intro s j
      let s' : Cocone (K ⋙ G) := (Cocone.precompose (Functor.whiskerLeft K r)).obj s
      simp only [Functor.mapCocone_pt, Functor.mapCocone_ι_app]
      change F.map (c.ι.app j) ≫ (i.app c.pt ≫ h.desc s') = s.ι.app j
      erw [← Category.assoc, i.naturality (c.ι.app j), Category.assoc]
      erw [h.fac]
      change i.app (K.obj j) ≫ (r.app (K.obj j) ≫ s.ι.app j) = s.ι.app j
      erw [← Category.assoc, hir, Category.id_comp]
    · intro s m hm
      let s' : Cocone (K ⋙ G) := (Cocone.precompose (Functor.whiskerLeft K r)).obj s
      simp only [Functor.mapCocone_pt, Functor.mapCocone_ι_app] at hm ⊢
      change F.obj c.pt ⟶ s.pt at m
      have hm' : r.app c.pt ≫ m =
          h.desc s' := by
        apply h.hom_ext
        intro j
        change G.map (c.ι.app j) ≫ (r.app c.pt ≫ m) = _
        erw [← Category.assoc, r.naturality (c.ι.app j), Category.assoc, hm]
        erw [h.fac]
        rfl
      change m = i.app c.pt ≫ h.desc s'
      erw [← hm', ← Category.assoc, hir, Category.id_comp]

/-- A retract of a flat right module is flat, by functoriality of the balanced tensor. -/
private theorem isFlat_of_retraction
    {D : Type*} [Category D] [MonoidalCategory D] [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X)]
    [∀ X : D, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)]
    {B : Mon D} {M M' : RightModule B}
    (i : M ⟶ M') (r : M' ⟶ M) (hi : i ≫ r = 𝟙 M) (hM' : IsFlat M') : IsFlat M := by
  let t : ∀ {P Q : RightModule B}, (P ⟶ Q) → (tensorFunctor P ⟶ tensorFunctor Q) :=
    fun {P Q} f ↦
      { app := fun N ↦ (_root_.Bimod.whiskerRight f N).hom
        naturality := fun N N' g ↦
          congrArg _root_.Bimod.Hom.hom (_root_.Bimod.whisker_exchange_bimod f g) }
  apply exactFunctor_of_retraction (t i) (t r) _ hM'
  ext N
  change ((tensorRightUnderlying N).map i) ≫ ((tensorRightUnderlying N).map r) = 𝟙 _
  rw [← Functor.map_comp, hi, Functor.map_id]

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable [MonoidalCategory (CochainComplex C ℤ)]
variable [MonoidalCategory (GradedObject ℤ C)]
variable [(CochainComplex.forgetToGraded C).LaxMonoidal]
variable [Preadditive (CochainComplex C ℤ)]
variable [MonoidalPreadditive (CochainComplex C ℤ)]

variable {A : Mon (CochainComplex C ℤ)}

namespace IsGradedFlat

variable [HasCoequalizers (GradedObject ℤ C)]
variable [∀ X : GradedObject ℤ C,
  PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X)]
variable [∀ X : GradedObject ℤ C,
  PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)]

/-- In an admissible short exact sequence, graded flatness of the left and middle terms implies
graded flatness of the right term. -/
@[stacks 0FSA "graded flatness of an admissible quotient"]
theorem of_left_middle (S : ShortComplex (RightModule A))
    (hS : IsAdmissibleShortExact S)
    (h₁ : IsGradedFlat S.X₁) (h₂ : IsGradedFlat S.X₂) :
    IsGradedFlat S.X₃ := by
  letI := hS.isAdmissibleEpi
  exact isFlat_of_retraction (section_ ((forgetToGradedRight A).map S.g))
    ((forgetToGradedRight A).map S.g) (IsSplitEpi.id _) h₂

/-- In an admissible short exact sequence, graded flatness of the outer terms implies graded
flatness of the middle term. -/
@[stacks 0FSA "graded flatness of an admissible extension"]
theorem of_left_right (S : ShortComplex (RightModule A))
    (hS : IsAdmissibleShortExact S)
    (h₁ : IsGradedFlat S.X₁) (h₃ : IsGradedFlat S.X₃) :
    IsGradedFlat S.X₂ := sorry

/-- In an admissible short exact sequence, graded flatness of the middle and right terms implies
graded flatness of the left term. -/
@[stacks 0FSA "graded flatness of an admissible kernel"]
theorem of_middle_right (S : ShortComplex (RightModule A))
    (hS : IsAdmissibleShortExact S)
    (h₂ : IsGradedFlat S.X₂) (h₃ : IsGradedFlat S.X₃) :
    IsGradedFlat S.X₁ := by
  letI := hS.isAdmissibleMono
  exact isFlat_of_retraction ((forgetToGradedRight A).map S.f)
    (retraction ((forgetToGradedRight A).map S.f)) (IsSplitMono.id _) h₂

end IsGradedFlat

namespace IsKFlat

variable [HasCoequalizers (CochainComplex C ℤ)]
variable [∀ X : CochainComplex C ℤ,
  PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X)]
variable [∀ X : CochainComplex C ℤ,
  PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)]

/-- In an admissible short exact sequence, relative K-flatness of the left and middle terms implies
relative K-flatness of the right term. -/
@[stacks 0FSA "relative K-flatness of an admissible quotient"]
theorem of_left_middle (S : ShortComplex (RightModule A))
    (hS : IsAdmissibleShortExact S)
    (h₁ : IsKFlat S.X₁) (h₂ : IsKFlat S.X₂) :
    IsKFlat S.X₃ := sorry

/-- In an admissible short exact sequence, relative K-flatness of the outer terms implies relative
K-flatness of the middle term. -/
@[stacks 0FSA "relative K-flatness of an admissible extension"]
theorem of_left_right (S : ShortComplex (RightModule A))
    (hS : IsAdmissibleShortExact S)
    (h₁ : IsKFlat S.X₁) (h₃ : IsKFlat S.X₃) :
    IsKFlat S.X₂ := sorry

/-- In an admissible short exact sequence, relative K-flatness of the middle and right terms implies
relative K-flatness of the left term. -/
@[stacks 0FSA "relative K-flatness of an admissible kernel"]
theorem of_middle_right (S : ShortComplex (RightModule A))
    (hS : IsAdmissibleShortExact S)
    (h₂ : IsKFlat S.X₂) (h₃ : IsKFlat S.X₃) :
    IsKFlat S.X₁ := sorry

end IsKFlat

namespace IsGoodAtBase

variable [HasCoequalizers (CochainComplex C ℤ)]
variable [∀ X : CochainComplex C ℤ,
  PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X)]
variable [∀ X : CochainComplex C ℤ,
  PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)]

variable [HasCoequalizers (GradedObject ℤ C)]
variable [∀ X : GradedObject ℤ C,
  PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X)]
variable [∀ X : GradedObject ℤ C,
  PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)]

/-- In an admissible short exact sequence, fixed-base goodness of the left and middle terms implies
fixed-base goodness of the right term. -/
@[stacks 0FSA "fixed-base goodness of an admissible quotient"]
theorem of_left_middle (S : ShortComplex (RightModule A))
    (hS : IsAdmissibleShortExact S)
    (h₁ : IsGoodAtBase S.X₁) (h₂ : IsGoodAtBase S.X₂) :
    IsGoodAtBase S.X₃ := by
  exact ⟨IsGradedFlat.of_left_middle S hS h₁.1 h₂.1,
    IsKFlat.of_left_middle S hS h₁.2 h₂.2⟩

/-- In an admissible short exact sequence, fixed-base goodness of the outer terms implies
fixed-base goodness of the middle term. -/
@[stacks 0FSA "fixed-base goodness of an admissible extension"]
theorem of_left_right (S : ShortComplex (RightModule A))
    (hS : IsAdmissibleShortExact S)
    (h₁ : IsGoodAtBase S.X₁) (h₃ : IsGoodAtBase S.X₃) :
    IsGoodAtBase S.X₂ := by
  exact ⟨IsGradedFlat.of_left_right S hS h₁.1 h₃.1,
    IsKFlat.of_left_right S hS h₁.2 h₃.2⟩

/-- In an admissible short exact sequence, fixed-base goodness of the middle and right terms implies
fixed-base goodness of the left term. -/
@[stacks 0FSA "fixed-base goodness of an admissible kernel"]
theorem of_middle_right (S : ShortComplex (RightModule A))
    (hS : IsAdmissibleShortExact S)
    (h₂ : IsGoodAtBase S.X₂) (h₃ : IsGoodAtBase S.X₃) :
    IsGoodAtBase S.X₁ := by
  exact ⟨IsGradedFlat.of_middle_right S hS h₂.1 h₃.1,
    IsKFlat.of_middle_right S hS h₂.2 h₃.2⟩

end IsGoodAtBase

end CategoryTheory.Bimod

end
