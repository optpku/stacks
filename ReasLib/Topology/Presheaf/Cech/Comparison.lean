/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Presheaf.Cech.Basic
public import ReasLib.CategoryTheory.Sites.Torsor.IsoClasses
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Image comparisons for Cech cohomology

This leaf separates the reusable shape of a comparison map from any particular cohomology
construction.  A comparison is an injective map whose range is the image of a distinguished class
map on a specified subset.  The cover-specialized view uses the canonical subset of torsor
isomorphism classes which are trivial on a family.  No chapter file, H¹ construction, or chosen
inverse is imported here.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open CategoryTheory.Sheaf

noncomputable section

universe uα uβ uγ w v u uι

namespace TopCat.Presheaf.Cech.Comparison

variable {α : Type uα} {β : Type uβ} {γ : Type uγ}

/-- A map is a comparison when it is injective and its range is the image of `κ` on `S`. -/
@[stacks 0B8R "generic injective-image comparison predicate"]
def IsComparison (τ : α → β) (κ : γ → β) (S : Set γ) : Prop :=
  Function.Injective τ ∧ Set.range τ = κ '' S

/-- A comparison map is injective. -/
@[stacks 0B8R "generic comparison injectivity"]
theorem IsComparison.injective {τ : α → β} {κ : γ → β} {S : Set γ}
    (hτ : IsComparison τ κ S) : Function.Injective τ := sorry

/-- The distinguished image of a comparison is its range. -/
@[stacks 0B8R "generic comparison image equality"]
theorem IsComparison.image_eq_range {τ : α → β} {κ : γ → β} {S : Set γ}
    (hτ : IsComparison τ κ S) : κ '' S = Set.range τ := sorry

/-- Range membership for a comparison is represented by an element of its distinguished image. -/
@[stacks 0B8R "generic comparison range membership"]
theorem IsComparison.mem_range_iff {τ : α → β} {κ : γ → β} {S : Set γ}
    (hτ : IsComparison τ κ S) (y : β) :
    y ∈ Set.range τ ↔ ∃ x : γ, x ∈ S ∧ κ x = y := sorry

section Torsor

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {G : CategoryTheory.Sheaf J GrpCat.{w}} {ι : Type uι}

/-- A comparison on a family `V` has range exactly the image of cover-trivial torsor classes under
the class map `κ`.  The family is not assumed to cover the ambient object; that hypothesis belongs
to the theorem which constructs a comparison. -/
@[stacks 0B8R "comparison with cover-trivial torsor image"]
def IsCoverComparison (V : ι → C) (τ : α → β)
    (κ : CategoryTheory.Sheaf.Torsor.IsoClasses G → β) : Prop :=
  Function.Injective τ ∧
    Set.range τ = CategoryTheory.Sheaf.Torsor.IsoClasses.imageOnCover V κ

/-- The cover comparison is the generic comparison for the cover-trivial class subset. -/
@[stacks 0B8R "cover comparison as a generic image comparison"]
theorem isCoverComparison_iff_isComparison {V : ι → C} {τ : α → β}
    {κ : CategoryTheory.Sheaf.Torsor.IsoClasses G → β} :
    IsCoverComparison V τ κ ↔
      IsComparison τ κ (CategoryTheory.Sheaf.Torsor.IsoClasses.trivialOnCover V) := sorry

/-- A cover comparison map is injective. -/
@[stacks 0B8R "injectivity of the cover comparison"]
theorem IsCoverComparison.injective {V : ι → C} {τ : α → β}
    {κ : CategoryTheory.Sheaf.Torsor.IsoClasses G → β}
    (hτ : IsCoverComparison V τ κ) : Function.Injective τ := sorry

/-- The range of a cover comparison is the image of its cover-trivial torsor classes. -/
@[stacks 0B8R "cover-trivial torsor image description"]
theorem IsCoverComparison.image_eq_range {V : ι → C} {τ : α → β}
    {κ : CategoryTheory.Sheaf.Torsor.IsoClasses G → β}
    (hτ : IsCoverComparison V τ κ) :
    CategoryTheory.Sheaf.Torsor.IsoClasses.imageOnCover V κ = Set.range τ := sorry

/-- Range membership for a cover comparison is represented by a cover-trivial torsor class. -/
@[stacks 0B8R "cover comparison range membership"]
theorem IsCoverComparison.mem_range_iff {V : ι → C} {τ : α → β}
    {κ : CategoryTheory.Sheaf.Torsor.IsoClasses G → β}
    (hτ : IsCoverComparison V τ κ) (y : β) :
    y ∈ Set.range τ ↔
      ∃ P : CategoryTheory.Sheaf.Torsor.IsoClasses G,
        CategoryTheory.Sheaf.Torsor.IsoClasses.IsTrivialOnCover V P ∧ κ P = y := sorry

/-- The cover comparison predicate in its source-facing existential image form. -/
@[stacks 0B8R "cover comparison existential specification"]
theorem isCoverComparison_iff {V : ι → C} {τ : α → β}
    {κ : CategoryTheory.Sheaf.Torsor.IsoClasses G → β} :
    IsCoverComparison V τ κ ↔
      Function.Injective τ ∧
        ∀ y : β, y ∈ Set.range τ ↔
          ∃ P : CategoryTheory.Sheaf.Torsor.IsoClasses G,
            CategoryTheory.Sheaf.Torsor.IsoClasses.IsTrivialOnCover V P ∧ κ P = y := sorry

end Torsor


end TopCat.Presheaf.Cech.Comparison

end
