/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import ReasLib.CategoryTheory.Filtration.HomologicalComplex.Functors
public import ReasLib.CategoryTheory.Filtration.Complete

/-!
# Homology of Filtered Homological Complexes

This file gives the induced-homology API for a homological complex in filtered objects.  The
shape-independent stage and graded-piece functors are owned by `HomologicalComplex/Functors`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u w

namespace CategoryTheory
namespace HomologicalComplex.Filtered

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {ι : Type w} {c : ComplexShape ι}

namespace Homology

variable [CategoryWithHomology C]

/-- The homology map induced by inclusion of filtration stage `p` in degree `i`. -/
@[stacks 012E "stagewise homology map"]
noncomputable abbrev map
    (K : HomologicalComplex (FilteredObject C) c) (p : ℤ) (i : ι) :
    (Stage.complex K p).homology i ⟶ (underlying K).homology i :=
  HomologicalComplex.homologyMap (Stage.inclusion K p) i

/-- The homology map from a later filtration stage factors through every earlier stage. -/
theorem map_factorization
    (K : HomologicalComplex (FilteredObject C) c) {p q : ℤ} (hpq : p ≤ q) (i : ι) :
    map K q i =
      HomologicalComplex.homologyMap (Stage.comparison K hpq) i ≫ map K p i := sorry

/-- Stagewise homology maps commute with every morphism of filtered homological complexes. -/
@[reassoc, stacks 012E "naturality of stagewise homology maps"]
theorem map_naturality {K L : HomologicalComplex (FilteredObject C) c}
    (f : K ⟶ L) (p : ℤ) (i : ι) :
    HomologicalComplex.homologyMap (Stage.map f p) i ≫ map L p i =
      map K p i ≫ HomologicalComplex.homologyMap (underlyingMap f) i := sorry

namespace Filtration

variable [HasImages C]

/-- The images of the stagewise homology maps form a decreasing family of subobjects. -/
theorem induced_antitone
    (K : HomologicalComplex (FilteredObject C) c) (i : ι) :
    Antitone (fun p : ℤ ↦ imageSubobject (Homology.map K p i)) := sorry

/-- The decreasing filtration on homology induced by the filtration-stage inclusions. -/
@[stacks 012E "induced homology filtration of a filtered homological complex"]
noncomputable def induced
    (K : HomologicalComplex (FilteredObject C) c) (i : ι) :
    DecreasingFiltration ((underlying K).homology i) where
  toFun p := imageSubobject (Homology.map K p i)
  monotone' _ _ hpq := induced_antitone K i hpq

/-- The `p`-th induced homology-filtration stage is the image of the stagewise homology map. -/
theorem induced_stage
    (K : HomologicalComplex (FilteredObject C) c) (i : ι) (p : ℤ) :
    (induced K i).stage p = imageSubobject (Homology.map K p i) := sorry

/-- The induced homology filtrations are exhaustive in every homological degree. -/
@[stacks 012E "exhaustive induced homology filtrations"]
def IsExhaustive (K : HomologicalComplex (FilteredObject C) c) : Prop :=
  ∀ i : ι, IndexedFiltration.IsExhaustive (induced K i)

section ZeroObject

variable [HasZeroObject C]

/-- The induced homology filtrations are separated in every homological degree. -/
@[stacks 012E "separated induced homology filtrations"]
def IsSeparated (K : HomologicalComplex (FilteredObject C) c) : Prop :=
  ∀ i : ι, IndexedFiltration.IsSeparated (induced K i)

/-- The induced homology filtrations are separated and exhaustive in every homological degree. -/
@[stacks 012E "separated and exhaustive induced homology filtrations"]
def IsSeparatedExhaustive (K : HomologicalComplex (FilteredObject C) c) : Prop :=
  IsSeparated K ∧ IsExhaustive K

/-- The induced homology filtrations are finite in every homological degree. -/
@[stacks 012E "finite induced homology filtrations"]
def IsFinite (K : HomologicalComplex (FilteredObject C) c) : Prop :=
  ∀ i : ι, IndexedFiltration.IsFinite (induced K i)

end ZeroObject

section Complete

variable [HasCokernels C]

/-- The induced homology filtrations are complete in every homological degree. -/
@[stacks 012E "complete induced homology filtrations"]
def IsComplete (K : HomologicalComplex (FilteredObject C) c) : Prop :=
  ∀ i : ι, DecreasingFiltration.IsComplete (induced K i)

end Complete

end Filtration

end Homology

end HomologicalComplex.Filtered
end CategoryTheory
