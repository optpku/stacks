/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Basic

/-!
# Point blowup sequences

A point blowup sequence records a compatible tower of blowups together with a
lifted morphism and its marked point at every stage.
-/

@[expose] public section

open CategoryTheory
open Topology

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A sequence of blowups at the successive images of a marked point under compatible lifts of
a scheme morphism. -/
structure PointBlowupSequence {T X : Scheme.{u}} (a : T ⟶ X) (t : T) where
  /-- The scheme at each stage of the sequence. -/
  stage : ℕ → Scheme.{u}
  /-- The blowup morphism from one stage to the preceding stage. -/
  step : ∀ i, stage (i + 1) ⟶ stage i
  /-- The compatible lift of the original morphism to each stage. -/
  arc : ∀ i, T ⟶ stage i
  /-- The image of the marked point at each stage. -/
  point : ∀ i, stage i
  /-- The reduced closed point used as the center at each stage. -/
  center : ∀ i, (stage i).IdealSheafData
  /-- The identification of the initial stage with the target of the original morphism. -/
  baseIso : stage 0 ≅ X
  /-- At stage zero, the lifted morphism agrees with the original morphism. -/
  arc_zero : arc 0 ≫ baseIso.hom = a
  /-- Each lifted morphism factors through the preceding one. -/
  arc_succ : ∀ i, arc (i + 1) ≫ step i = arc i
  /-- The marked point is the image of the source point under the lifted morphism. -/
  point_eq : ∀ i, point i = arc i t
  /-- Every marked point is closed. -/
  point_isClosed : ∀ i, IsClosed ({point i} : Set (stage i))
  /-- The center is the reduced closed subscheme supported at the marked point. -/
  center_eq : ∀ i, center i = Scheme.IdealSheafData.vanishingIdeal
    ⟨{point i}, point_isClosed i⟩
  /-- Every transition morphism is the blowup in its specified center. -/
  step_isBlowup : ∀ i, IsBlowup (step i) (center i)

namespace PointBlowupSequence

/-- Construct a point blowup sequence from compatible stages and lifted morphisms, using the
reduced vanishing ideal of each image point as its center. -/
noncomputable def fromTower {T X : Scheme.{u}} (a : T ⟶ X) (t : T)
    (stage : ℕ → Scheme.{u}) (step : ∀ i, stage (i + 1) ⟶ stage i)
    (arc : ∀ i, T ⟶ stage i) (baseIso : stage 0 ≅ X)
    (arc_zero : arc 0 ≫ baseIso.hom = a)
    (arc_succ : ∀ i, arc (i + 1) ≫ step i = arc i)
    (point_isClosed : ∀ i, IsClosed ({arc i t} : Set (stage i)))
    (step_isBlowup : ∀ i, IsBlowup (step i)
      (Scheme.IdealSheafData.vanishingIdeal ⟨{arc i t}, point_isClosed i⟩)) :
    PointBlowupSequence a t where
  stage := stage
  step := step
  arc := arc
  point := fun i ↦ arc i t
  center := fun i ↦ Scheme.IdealSheafData.vanishingIdeal
    ⟨{arc i t}, point_isClosed i⟩
  baseIso := baseIso
  arc_zero := arc_zero
  arc_succ := arc_succ
  point_eq := sorry
  point_isClosed := point_isClosed
  center_eq := sorry
  step_isBlowup := step_isBlowup

/-- The point of a sequence built by `fromTower` is the image of the marked source point. -/
theorem fromTower_point {T X : Scheme.{u}} (a : T ⟶ X) (t : T)
    (stage : ℕ → Scheme.{u}) (step : ∀ i, stage (i + 1) ⟶ stage i)
    (arc : ∀ i, T ⟶ stage i) (baseIso : stage 0 ≅ X)
    (arc_zero : arc 0 ≫ baseIso.hom = a)
    (arc_succ : ∀ i, arc (i + 1) ≫ step i = arc i)
    (point_isClosed : ∀ i, IsClosed ({arc i t} : Set (stage i)))
    (step_isBlowup : ∀ i, IsBlowup (step i)
      (Scheme.IdealSheafData.vanishingIdeal ⟨{arc i t}, point_isClosed i⟩)) (i : ℕ) :
    (fromTower a t stage step arc baseIso arc_zero arc_succ point_isClosed
      step_isBlowup).point i = arc i t := sorry

/-- The center of a sequence built by `fromTower` is the reduced vanishing ideal of its image
point. -/
theorem fromTower_center {T X : Scheme.{u}} (a : T ⟶ X) (t : T)
    (stage : ℕ → Scheme.{u}) (step : ∀ i, stage (i + 1) ⟶ stage i)
    (arc : ∀ i, T ⟶ stage i) (baseIso : stage 0 ≅ X)
    (arc_zero : arc 0 ≫ baseIso.hom = a)
    (arc_succ : ∀ i, arc (i + 1) ≫ step i = arc i)
    (point_isClosed : ∀ i, IsClosed ({arc i t} : Set (stage i)))
    (step_isBlowup : ∀ i, IsBlowup (step i)
      (Scheme.IdealSheafData.vanishingIdeal ⟨{arc i t}, point_isClosed i⟩)) (i : ℕ) :
    (fromTower a t stage step arc baseIso arc_zero arc_succ point_isClosed
      step_isBlowup).center i =
      Scheme.IdealSheafData.vanishingIdeal ⟨{arc i t}, point_isClosed i⟩ := sorry

/-- Discard the initial stage of a point blowup sequence. -/
def tail {T X : Scheme.{u}} {a : T ⟶ X} {t : T} (S : PointBlowupSequence a t) :
    PointBlowupSequence (S.arc 1) t where
  stage := fun i ↦ S.stage (i + 1)
  step := fun i ↦ S.step (i + 1)
  arc := fun i ↦ S.arc (i + 1)
  point := fun i ↦ S.point (i + 1)
  center := fun i ↦ S.center (i + 1)
  baseIso := Iso.refl _
  arc_zero := sorry
  arc_succ := sorry
  point_eq := sorry
  point_isClosed := fun i ↦ S.point_isClosed (i + 1)
  center_eq := sorry
  step_isBlowup := fun i ↦ S.step_isBlowup (i + 1)

/-- The stages of the tail are the stages of the original sequence shifted by one. -/
theorem tail_stage {T X : Scheme.{u}} {a : T ⟶ X} {t : T}
    (S : PointBlowupSequence a t) (i : ℕ) : S.tail.stage i = S.stage (i + 1) := sorry

/-- The marked points of the tail are the marked points of the original sequence shifted by one. -/
theorem tail_point {T X : Scheme.{u}} {a : T ⟶ X} {t : T}
    (S : PointBlowupSequence a t) (i : ℕ) : S.tail.point i = S.point (i + 1) := sorry

/-- Each transition in a point blowup sequence is a blowup in its stored reduced point center. -/
theorem isBlowup_step {T X : Scheme.{u}} {a : T ⟶ X} {t : T}
    (S : PointBlowupSequence a t) (i : ℕ) : IsBlowup (S.step i) (S.center i) := sorry

end PointBlowupSequence

end AlgebraicGeometry.Scheme.Hom
