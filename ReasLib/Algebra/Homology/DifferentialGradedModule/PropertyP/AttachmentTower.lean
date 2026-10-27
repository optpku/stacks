/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyP.CellAttachment

/-!
# Private proposal: the actual finite stages of the all-pairs attachment tower

This file constructs the initial augmentation, every successor augmentation, and their
functorial maps. It does not assert that a finite stage is a resolution.
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits

namespace DifferentialGradedModule.PropertyP.PrivateConstruction

variable {R : Type u} [CommRing R] {A : CochainDGAlgebra.{u, v} R}

/-- An actual DG module equipped with its actual augmentation to `M`. -/
structure Augmented (M : DifferentialGradedModule.{u, v} A) where
  obj : DifferentialGradedModule.{u, v} A
  π : obj ⟶ M

/-- A specified commuting square between augmentations. -/
structure AugmentedMap {M N : DifferentialGradedModule.{u, v} A}
    (f : M ⟶ N) (P : Augmented M) (Q : Augmented N) where
  hom : P.obj ⟶ Q.obj
  naturality : hom ≫ Q.π = P.π ≫ f

/-- Start with the actual free module on all cycles. -/
def initialAugmented (M : DifferentialGradedModule.{u, v} A) : Augmented M :=
  ⟨initial M, initialπ M⟩

/-- Adjoin all the specified cycle/image pairs in one step. -/
def next {M : DifferentialGradedModule.{u, v} A} (P : Augmented M) : Augmented M :=
  ⟨attach P.π, attachπ P.π⟩

/-- The all-pairs attachment operation maps commuting squares using both actual maps. -/
def nextMap {M N : DifferentialGradedModule.{u, v} A} {f : M ⟶ N}
    {P : Augmented M} {Q : Augmented N} (g : AugmentedMap f P Q) :
    AugmentedMap f (next P) (next Q) where
  hom := attachMap g.hom f g.naturality
  naturality := attachMap_naturality g.hom f g.naturality

/-- Every finite stage is a recursively specified DG module with a specified augmentation. -/
def stage (M : DifferentialGradedModule.{u, v} A) : ℕ → Augmented M
  | 0 => initialAugmented M
  | n + 1 => next (stage M n)

/-- Consecutive stages are connected by the literal first-coordinate inclusion. -/
def step (M : DifferentialGradedModule.{u, v} A) (n : ℕ) :
    (stage M n).obj ⟶ (stage M (n + 1)).obj :=
  inclusion (stage M n).π

/-- Each stage comparison is recursively obtained from the actual map on cycle/pair labels. -/
def stageMap {M N : DifferentialGradedModule.{u, v} A} (f : M ⟶ N) :
    ∀ n, AugmentedMap f (stage M n) (stage N n)
  | 0 => ⟨initialMap f, initialMap_naturality f⟩
  | n + 1 => nextMap (stageMap f n)

/-- The functor sending a target to a specified finite stage. -/
def stageFunctor (A : CochainDGAlgebra.{u, v} R) (n : ℕ) :
    DifferentialGradedModule.{u, v} A ⥤ DifferentialGradedModule.{u, v} A where
  obj M := (stage M n).obj
  map f := (stageMap f n).hom
  map_id := by sorry
  map_comp := by sorry

/-- The actual augmentation is natural at every finite stage. -/
def stageAugmentation (A : CochainDGAlgebra.{u, v} R) (n : ℕ) :
    stageFunctor A n ⟶ 𝟭 (DifferentialGradedModule.{u, v} A) where
  app M := (stage M n).π
  naturality _ _ f := (stageMap f n).naturality

/-- The tower's transition inclusions commute with augmentation. -/
theorem step_π (M : DifferentialGradedModule.{u, v} A) (n : ℕ) :
    step M n ≫ (stage M (n + 1)).π = (stage M n).π :=
  inclusion_attachπ (stage M n).π

/-- The transition inclusions commute with all induced stage maps. -/
theorem step_naturality {M N : DifferentialGradedModule.{u, v} A}
    (f : M ⟶ N) (n : ℕ) :
    step M n ≫ (stageMap f (n + 1)).hom = (stageMap f n).hom ≫ step N n := by sorry

/-- The free piece presented by stage zero has its concrete coproduct isomorphism. -/
def initialPiece (M : DifferentialGradedModule.{u, v} A) : Piece A (stage M 0).obj :=
  freePiece (fun i : CycleIndex M ↦ i.1)

/-- Every successor quotient has its explicitly labelled coproduct presentation. -/
def successorPiece (M : DifferentialGradedModule.{u, v} A) (n : ℕ) :
    Piece A (newCells (stage M n).π) :=
  freePiece (fun i : AttachIndex (stage M n).π ↦ i.degree)

/-- The literal quotient projection of a successor stage. -/
def stepProjection (M : DifferentialGradedModule.{u, v} A) (n : ℕ) :
    (stage M (n + 1)).obj ⟶ newCells (stage M n).π :=
  projection (stage M n).π

/-- Inclusion followed by projection is zero. -/
theorem step_projection_zero (M : DifferentialGradedModule.{u, v} A) (n : ℕ) :
    step M n ≫ stepProjection M n = 0 := by sorry

/-- The displayed pair of maps is a short exact row. -/
theorem step_shortExact (M : DifferentialGradedModule.{u, v} A) (n : ℕ) :
    (ShortComplex.mk (step M n) (stepProjection M n) (step_projection_zero M n)).ShortExact := by
  sorry

/-- The splitting is by graded `A`-maps; it needs no field or nonzero-ring assumption. -/
theorem step_admissible (M : DifferentialGradedModule.{u, v} A) (n : ℕ) :
    IsAdmissibleMono (step M n) := by sorry

end DifferentialGradedModule.PropertyP.PrivateConstruction
