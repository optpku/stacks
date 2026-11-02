/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fppf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Syntomic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtalePrecoverage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sites.FpqcPrecoverage

/-!
# Base change of properties local on the target

This file records that a morphism property of algebraic spaces over a scheme `S`
which is local on the target for the fpqc, fppf, syntomic, smooth, or étale
precoverage is preserved by base change along a single morphism of the
corresponding covering type.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- The smooth precoverage on algebraic spaces over `S`: jointly surjective families
of smooth morphisms. -/
abbrev smoothPrecoverage (S : Scheme.{u}) : Precoverage (AlgebraicSpace S) :=
  precoverage (@Smooth S)

/-- The syntomic precoverage on algebraic spaces over `S`: jointly surjective
families of syntomic morphisms. -/
abbrev syntomicPrecoverage (S : Scheme.{u}) : Precoverage (AlgebraicSpace S) :=
  precoverage (@Syntomic S)

/-- An indexed family belongs to `smoothPrecoverage` if and only if each morphism is
smooth and `|X|` equals the union of the images `Points.map (f i)`. -/
theorem ofArrows_mem_smoothPrecoverage_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {Xᵢ : ι → AlgebraicSpace S} (f : ∀ i, Xᵢ i ⟶ X) :
    Presieve.ofArrows Xᵢ f ∈ (smoothPrecoverage S).coverings X ↔
      (∀ i, Smooth (f i)) ∧ (⋃ i, Set.range (Points.map (f i))) = Set.univ := by
  change (Presieve.ofArrows Xᵢ f ∈
      (Types.jointlySurjectivePrecoverage.comap pointsFunctor) X ∧
    Presieve.ofArrows Xᵢ f ∈ (MorphismProperty.precoverage (@Smooth S)) X) ↔ _
  rw [Presieve.ofArrows_mem_comap_jointlySurjectivePrecoverage_iff,
    MorphismProperty.ofArrows_mem_precoverage, Set.iUnion_eq_univ_iff]
  exact and_comm

/-- An indexed family belongs to `syntomicPrecoverage` if and only if each morphism
is syntomic and `|X|` equals the union of the images `Points.map (f i)`. -/
theorem ofArrows_mem_syntomicPrecoverage_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {Xᵢ : ι → AlgebraicSpace S} (f : ∀ i, Xᵢ i ⟶ X) :
    Presieve.ofArrows Xᵢ f ∈ (syntomicPrecoverage S).coverings X ↔
      (∀ i, Syntomic (f i)) ∧ (⋃ i, Set.range (Points.map (f i))) = Set.univ := by
  change (Presieve.ofArrows Xᵢ f ∈
      (Types.jointlySurjectivePrecoverage.comap pointsFunctor) X ∧
    Presieve.ofArrows Xᵢ f ∈ (MorphismProperty.precoverage (@Syntomic S)) X) ↔ _
  rw [Presieve.ofArrows_mem_comap_jointlySurjectivePrecoverage_iff,
    MorphismProperty.ofArrows_mem_precoverage, Set.iUnion_eq_univ_iff]
  exact and_comm

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.IsLocalAtTarget

variable {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
  {X Y X' Y' : AlgebraicSpace S}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {i : X' ⟶ X} {f' : X' ⟶ Y'}

-- A member of any covering family is an allowed base change for a target-local property.
private theorem of_isPullback_of_mem {K : Precoverage (AlgebraicSpace S)}
    [P.IsLocalAtTarget K] {R : Presieve Y}
    (sq : IsPullback i f' f g) (hR : R ∈ K Y) (hg : R g) (hf : P f) : P f' := by
  letI : HasPullback f g := sq.hasPullback
  rw [← P.cancel_left_of_respectsIso sq.isoPullback.inv, sq.isoPullback_inv_snd]
  exact MorphismProperty.IsLocalAtTarget.pullbackSnd hR hg hf

-- Adjoin the identity to make a jointly surjective family.
private theorem of_isPullback_precoverage (Q : MorphismProperty (AlgebraicSpace S))
    [P.IsLocalAtTarget (precoverage Q)] (hid : Q (𝟙 Y)) (hg : Q g)
    (sq : IsPullback i f' f g) (hf : P f) : P f' := by
  let R : Presieve Y := Presieve.singleton g ⊔ Presieve.singleton (𝟙 Y)
  have hR : R ∈ precoverage Q Y := by
    refine ⟨?_, ?_⟩
    · apply (Presieve.mem_comap_jointlySurjectivePrecoverage_iff pointsFunctor).mpr
      intro y
      exact ⟨Y, 𝟙 Y, Or.inr ⟨⟩, y, Points.map_id y⟩
    · intro T a ha
      change Presieve.singleton g a ∨ Presieve.singleton (𝟙 Y) a at ha
      rcases ha with ha | ha
      · cases ha
        exact hg
      · cases ha
        exact hid
  exact of_isPullback_of_mem sq hR (Or.inl ⟨⟩) hf

/-- An fpqc-local morphism property on the target is preserved by pullback along a
flat morphism. -/
theorem of_isPullback_fpqc
    [P.IsLocalAtTarget (fpqcPrecoverage S)] [Flat g]
    (sq : IsPullback i f' f g) (hf : P f) : P f' := by
  let U : Bool → AlgebraicSpace S := fun b ↦ match b with
    | false => Y
    | true => Y'
  let a : ∀ b, U b ⟶ Y := fun b ↦ match b with
    | false => 𝟙 Y
    | true => g
  let 𝒰 : SemiRepresentableFamily.Over.{u + 1} Y :=
    SemiRepresentableFamily.Over.ofArrows
      (fun b : ULift.{u + 1} Bool ↦ U b.down) (fun b ↦ a b.down)
  have h𝒰 : 𝒰.toPresieve ∈ fpqcPrecoverage S Y := by
    refine ⟨𝒰, ?_, rfl⟩
    refine ⟨?_, ?_⟩
    · rintro ⟨b⟩
      change Flat (a b)
      cases b
      · exact (inferInstance : Flat (𝟙 Y))
      · exact (inferInstance : Flat g)
    · intro Z hZ h
      let 𝒱 : StandardFpqcCover Z.left :=
        { isAffineTarget := hZ
          n := 1
          U := fun _ ↦ Z.left
          map := fun _ ↦ 𝟙 Z.left
          isAffine := fun _ ↦ hZ
          flat := fun _ ↦ inferInstance
          cover := fun z ↦ ⟨0, z, rfl⟩ }
      refine ⟨𝒱, ⟨{ α := fun _ ↦ ⟨false⟩, f := fun j ↦ ?_ }⟩⟩
      exact Over.homMk
        (pullback.lift (ofStandardFpqcCoverMap 𝒱 j)
          (ofStandardFpqcCoverMap 𝒱 j ≫ h)
          (by
            change _ = (ofStandardFpqcCoverMap 𝒱 j ≫ h) ≫ 𝟙 Y
            exact (Category.comp_id _).symm))
        (by
          change _ ≫ pullback.fst h (𝟙 Y) = ofStandardFpqcCoverMap 𝒱 j
          exact pullback.lift_fst _ _ _)
  have hg : 𝒰.toPresieve g := Presieve.ofArrows.mk (ULift.up true)
  exact of_isPullback_of_mem sq h𝒰 hg hf

/-- An fppf-local morphism property on the target is preserved by pullback along a
flat, locally finitely presented morphism. -/
theorem of_isPullback_fppf
    [P.IsLocalAtTarget (fppfPrecoverage S)] [Flat g]
    [LocallyOfFinitePresentation g]
    (sq : IsPullback i f' f g) (hf : P f) : P f' := by
  let R : Presieve Y := Presieve.singleton g ⊔ Presieve.singleton (𝟙 Y)
  have hR : R ∈ fppfPrecoverage S Y := by
    refine ⟨?_, ?_⟩
    · intro T a ha
      change Presieve.singleton g a ∨ Presieve.singleton (𝟙 Y) a at ha
      rcases ha with ha | ha
      · cases ha
        exact ⟨inferInstance, inferInstance⟩
      · cases ha
        exact ⟨inferInstance, inferInstance⟩
    · intro y
      exact ⟨Y, 𝟙 Y, Or.inr ⟨⟩, y, Points.map_id y⟩
  exact of_isPullback_of_mem sq hR (Or.inl ⟨⟩) hf

/-- A syntomic-local morphism property on the target is preserved by pullback along
a syntomic morphism. -/
theorem of_isPullback_syntomic
    [P.IsLocalAtTarget (syntomicPrecoverage S)] [Syntomic g]
    (sq : IsPullback i f' f g) (hf : P f) : P f' := by
  exact of_isPullback_precoverage (@Syntomic S) inferInstance inferInstance sq hf

/-- A smooth-local morphism property on the target is preserved by pullback along a
smooth morphism. -/
theorem of_isPullback_smooth
    [P.IsLocalAtTarget (smoothPrecoverage S)] [Smooth g]
    (sq : IsPullback i f' f g) (hf : P f) : P f' := by
  exact of_isPullback_precoverage (@Smooth S) inferInstance inferInstance sq hf

/-- An étale-local morphism property on the target is preserved by pullback along an
étale morphism. -/
theorem of_isPullback_etale
    [P.IsLocalAtTarget etalePrecoverage] [Etale g]
    (sq : IsPullback i f' f g) (hf : P f) : P f' := by
  letI : P.IsLocalAtTarget (precoverage (@Etale S)) :=
    (inferInstance : P.IsLocalAtTarget etalePrecoverage)
  exact of_isPullback_precoverage (@Etale S) inferInstance inferInstance sq hf

end AlgebraicGeometry.AlgebraicSpace.IsLocalAtTarget
