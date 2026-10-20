/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.Computation
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Sequences of Filtration Stages

An antitone sequence of integer filtration indices determines a sequential
diagram of stage complexes.  This file owns that neutral construction, its
canonical cocone to the underlying complex, and its functoriality in filtered
maps.  Concrete filtrations can specialize it without rebuilding transition
maps degree by degree.
-/

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory

noncomputable section

namespace FilteredComplex.StageSequence

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- The sequential diagram of stages selected by an antitone index function. -/
@[stacks 0D8Z]
def ofAntitone (K : FilteredComplex C) (p : ℕ → ℤ) (hp : Antitone p) :
    ℕ ⥤ CochainComplex C ℤ :=
  Functor.ofSequence (fun n ↦ K.stageComparison (hp (Nat.le_succ n)))

/-- The object at `n` in an antitone stage sequence is the stage at `p n`. -/
@[simp]
theorem ofAntitone_obj (K : FilteredComplex C) (p : ℕ → ℤ) (hp : Antitone p)
    (n : ℕ) :
    (ofAntitone K p hp).obj n = K.stage (p n) := sorry

/-- The successor map in an antitone stage sequence is the canonical stage comparison. -/
@[simp]
theorem ofAntitone_map_succ (K : FilteredComplex C) (p : ℕ → ℤ)
    (hp : Antitone p) (n : ℕ) :
    (ofAntitone K p hp).map (homOfLE (Nat.le_succ n)) =
      K.stageComparison (hp (Nat.le_succ n)) := sorry

/-- The stage inclusions satisfy the successor naturality relation for the
constant diagram at the underlying complex. -/
@[reassoc]
theorem toUnderlying_naturality (K : FilteredComplex C) (p : ℕ → ℤ)
    (hp : Antitone p) (n : ℕ) :
    (ofAntitone K p hp).map (homOfLE (Nat.le_succ n)) ≫
        K.stageInclusion (p (n + 1)) =
      K.stageInclusion (p n) ≫
        ((Functor.const ℕ).obj K.underlying).map (homOfLE (Nat.le_succ n)) := sorry

/-- The stage inclusions form a natural transformation to the constant
diagram at the underlying complex. -/
@[stacks 0D8Z]
def toUnderlying (K : FilteredComplex C) (p : ℕ → ℤ) (hp : Antitone p) :
    ofAntitone K p hp ⟶ (Functor.const ℕ).obj K.underlying :=
  NatTrans.ofSequence (fun n ↦ K.stageInclusion (p n))
    (toUnderlying_naturality K p hp)

/-- The `n`th component of the canonical transformation is the stage inclusion. -/
@[simp]
theorem toUnderlying_app (K : FilteredComplex C) (p : ℕ → ℤ)
    (hp : Antitone p) (n : ℕ) :
    (toUnderlying K p hp).app n = K.stageInclusion (p n) := sorry

/-- The canonical cocone from an antitone stage sequence to the underlying complex. -/
@[stacks 0D8Z]
def cocone (K : FilteredComplex C) (p : ℕ → ℤ) (hp : Antitone p) :
    Cocone (ofAntitone K p hp) :=
  Cocone.mk K.underlying (toUnderlying K p hp)

/-- The point of the canonical stage-sequence cocone is the underlying complex. -/
@[simp]
theorem cocone_pt (K : FilteredComplex C) (p : ℕ → ℤ) (hp : Antitone p) :
    (cocone K p hp).pt = K.underlying := sorry

/-- The legs of the canonical cocone are the stage inclusions. -/
@[simp]
theorem cocone_ι_app (K : FilteredComplex C) (p : ℕ → ℤ)
    (hp : Antitone p) (n : ℕ) :
    (cocone K p hp).ι.app n = K.stageInclusion (p n) := sorry

/-- A filtered morphism commutes with the stage comparisons selected by an
antitone sequence. -/
@[reassoc]
theorem map_naturality {K L : FilteredComplex C} (f : K ⟶ L)
    (p : ℕ → ℤ) (hp : Antitone p) (n : ℕ) :
    (ofAntitone K p hp).map (homOfLE (Nat.le_succ n)) ≫
        K.stageMap f (p (n + 1)) =
      K.stageMap f (p n) ≫
        (ofAntitone L p hp).map (homOfLE (Nat.le_succ n)) := sorry

/-- A filtered morphism induces a morphism between the corresponding stage sequences. -/
@[stacks 0D8Z]
def map {K L : FilteredComplex C} (f : K ⟶ L) (p : ℕ → ℤ)
    (hp : Antitone p) :
    ofAntitone K p hp ⟶ ofAntitone L p hp :=
  NatTrans.ofSequence (fun n ↦ K.stageMap f (p n)) (map_naturality f p hp)

/-- The component of the induced sequence map is the corresponding stage map. -/
@[simp]
theorem map_app {K L : FilteredComplex C} (f : K ⟶ L) (p : ℕ → ℤ)
    (hp : Antitone p) (n : ℕ) :
    (map f p hp).app n = K.stageMap f (p n) := sorry

/-- The induced sequence map of an identity filtered morphism is the identity. -/
@[simp]
theorem map_id (K : FilteredComplex C) (p : ℕ → ℤ) (hp : Antitone p) :
    map (𝟙 K) p hp = 𝟙 (ofAntitone K p hp) := sorry

/-- Passage to stage sequences preserves composition of filtered morphisms. -/
@[simp]
theorem map_comp {K L M : FilteredComplex C} (f : K ⟶ L) (g : L ⟶ M)
    (p : ℕ → ℤ) (hp : Antitone p) :
    map (f ≫ g) p hp = map f p hp ≫ map g p hp := sorry

/-- Taking the stages selected by an antitone index function is functorial in
the filtered complex. -/
@[stacks 0D8Z]
def functor (p : ℕ → ℤ) (hp : Antitone p) :
    FilteredComplex C ⥤ (ℕ ⥤ CochainComplex C ℤ) where
  obj K := ofAntitone K p hp
  map f := map f p hp
  map_id K := map_id K p hp
  map_comp f g := map_comp f g p hp

/-- Evaluating the stage-sequence functor gives the selected antitone diagram. -/
@[simp, stacks 0D8Z]
theorem functor_obj (K : FilteredComplex C) (p : ℕ → ℤ) (hp : Antitone p) :
    (functor p hp).obj K = ofAntitone K p hp := sorry

/-- The map of the stage-sequence functor is the termwise stage map. -/
@[simp, stacks 0D8Z]
theorem functor_map {K L : FilteredComplex C} (f : K ⟶ L)
    (p : ℕ → ℤ) (hp : Antitone p) :
    (functor p hp).map f = map f p hp := sorry

/-- The sequence map and the underlying map commute with the canonical
transformations to the underlying complexes. -/
@[reassoc, stacks 0D8Z]
theorem map_comp_toUnderlying {K L : FilteredComplex C} (f : K ⟶ L)
    (p : ℕ → ℤ) (hp : Antitone p) :
    map f p hp ≫ toUnderlying L p hp =
      toUnderlying K p hp ≫ (Functor.const ℕ).map (K.underlyingMap f) := sorry

end FilteredComplex.StageSequence

end

end CategoryTheory
