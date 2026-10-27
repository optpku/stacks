/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Generator.Subobject
public import ReasLib.CategoryTheory.Subobject.Cardinal
public import ReasLib.CategoryTheory.Subobject.Image
public import ReasLib.CategoryTheory.Subobject.Pullback

@[expose] public section

/-!
# Small Epi Refinements from a Separator

Given an epimorphism `π : M ⟶ N` and a separator `U`, this module organizes the standard family
of maps from `U` which avoids the pullbacks of proper subobjects of `N`.  A small coproduct of this
family maps to `M`; its image is a subobject of `M` which still maps epimorphically to `N`.

The arbitrary choices are isolated in `SeparatorEpi.Family`.  All subsequent maps and subobjects
are explicit constructions from a supplied family.
-/

open CategoryTheory Limits

universe w v u

namespace CategoryTheory.SeparatorEpi

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {U M N : C}

/-- The subobject of `N` represented by a point of the canonical small model of `Subobject N`. -/
noncomputable abbrev subobjectAt [Small.{w} (Subobject N)]
    (i : Shrink.{w} (Subobject N)) : Subobject N :=
  (equivShrink (Subobject N)).symm i

/-- The construction-specific bound: the subobject cardinal of the coproduct from which a
separator test family is assembled. -/
noncomputable abbrev familyBound
    [Small.{w} (Subobject N)] [HasCoproduct fun _ : Shrink.{w} (Subobject N) ↦ U] :
    Cardinal :=
  Cardinal.mk (Subobject (∐ fun _ : Shrink.{w} (Subobject N) ↦ U))

/-- A family of maps from `U` to the source of `π` which, for every proper subobject of the
target, avoids its pullback.  The component at the top subobject is normalized to zero. -/
@[stacks 079J "separator test family"]
structure Family (U : C) {M N : C} (π : M ⟶ N) [Small.{w} (Subobject N)] where
  /-- The selected map at a point of the small subobject index. -/
  component (i : Shrink.{w} (Subobject N)) : U ⟶ M
  /-- The selected component at the top subobject is zero. -/
  component_eq_zero (i : Shrink.{w} (Subobject N)) (hi : subobjectAt i = ⊤) :
    component i = 0
  /-- A component indexed by a proper subobject does not factor through its pullback. -/
  not_factors (i : Shrink.{w} (Subobject N)) (hi : subobjectAt i ≠ ⊤) :
    ¬ ((Subobject.pullback π).obj (subobjectAt i)).Factors (component i)

namespace Family

section Choice

variable [Small.{w} (Subobject N)]

/-- Select a detecting separator map for each proper pullback subobject, and zero at the top. -/
noncomputable def ofSeparator (hU : IsSeparator U) (π : M ⟶ N) [Epi π] :
    Family U π := by
  classical
  let witness (i : Shrink.{w} (Subobject N)) (hi : subobjectAt i ≠ ⊤) :=
    (isSeparator_iff_exists_not_factors_subobject C U).mp hU
      ((Subobject.pullback π).obj (subobjectAt i))
      (Subobject.pullback_ne_top_of_epi π hi)
  exact
    { component := fun i ↦ if hi : subobjectAt i = ⊤ then 0 else (witness i hi).choose
      component_eq_zero := fun i hi ↦ dif_pos hi
      not_factors := fun i hi ↦ by
        simp only [dif_neg hi]
        exact (witness i hi).choose_spec }

/-- An epimorphism and a separator determine a nonempty type of separator test families. -/
theorem nonempty (hU : IsSeparator U) (π : M ⟶ N) [Epi π] :
    Nonempty (Family U π) := ⟨ofSeparator hU π⟩

end Choice

section Construction

variable {π : M ⟶ N} [Small.{w} (Subobject N)]
variable [HasCoproduct fun _ : Shrink.{w} (Subobject N) ↦ U]

/-- The coproduct map assembled from the components of a separator test family. -/
@[stacks 079J "shrink-indexed coproduct map"]
noncomputable def map (F : Family U π) :
    (∐ fun _ : Shrink.{w} (Subobject N) ↦ U) ⟶ M :=
  Sigma.desc F.component

/-- The coproduct injection followed by `F.map` is the corresponding selected component. -/
@[reassoc (attr := simp)]
theorem ι_map (F : Family U π) (i : Shrink.{w} (Subobject N)) :
    Sigma.ι (fun _ : Shrink.{w} (Subobject N) ↦ U) i ≫ F.map = F.component i :=
  Sigma.ι_desc _ _

/-- The image of the shrink-indexed coproduct map, regarded as a subobject of `M`. -/
@[stacks 079J "refinement subobject"]
noncomputable def refinement (F : Family U π) : Subobject M :=
  imageSubobject F.map

/-- The canonical epimorphism from the coproduct onto the refinement subobject. -/
noncomputable abbrev toRefinement (F : Family U π) :
    (∐ fun _ : Shrink.{w} (Subobject N) ↦ U) ⟶ (F.refinement : C) :=
  factorThruImageSubobject F.map

/-- The canonical map to the refinement followed by its inclusion is the coproduct map. -/
@[reassoc (attr := simp)]
theorem toRefinement_arrow (F : Family U π) :
    F.toRefinement ≫ F.refinement.arrow = F.map := imageSubobject_arrow_comp F.map

/-- The selected component, regarded as a map into the refinement subobject. -/
noncomputable abbrev componentLift (F : Family U π) (i : Shrink.{w} (Subobject N)) :
    U ⟶ (F.refinement : C) :=
  Sigma.ι (fun _ : Shrink.{w} (Subobject N) ↦ U) i ≫ F.toRefinement

/-- Each selected component factors through the refinement subobject. -/
@[reassoc (attr := simp)]
theorem componentLift_arrow (F : Family U π) (i : Shrink.{w} (Subobject N)) :
    F.componentLift i ≫ F.refinement.arrow = F.component i := by
  rw [componentLift, Category.assoc, toRefinement_arrow, ι_map]

/-- Factorization-predicate view of `componentLift_arrow`. -/
theorem component_factors_refinement (F : Family U π) (i : Shrink.{w} (Subobject N)) :
    F.refinement.Factors (F.component i) :=
  (Subobject.factors_iff _ _).mpr ⟨F.componentLift i, F.componentLift_arrow i⟩

/-- The morphism from the refinement subobject to the original target. -/
@[stacks 079J "refinement-to-target map"]
noncomputable abbrev toTarget (F : Family U π) : (F.refinement : C) ⟶ N :=
  F.refinement.arrow ≫ π

/-- The coproduct map factors through the refinement-to-target morphism. -/
@[reassoc (attr := simp)]
theorem toRefinement_toTarget (F : Family U π) :
    F.toRefinement ≫ F.toTarget = F.map ≫ π := by
  rw [toTarget, ← Category.assoc, toRefinement_arrow]

/-- Each lifted component followed by the refinement-to-target map is its original composite
with `π`. -/
@[reassoc (attr := simp)]
theorem componentLift_toTarget (F : Family U π) (i : Shrink.{w} (Subobject N)) :
    F.componentLift i ≫ F.toTarget = F.component i ≫ π := by
  rw [toTarget, ← Category.assoc, componentLift_arrow]

/-- The image of the refinement-to-target map is the top subobject. -/
theorem image_toTarget_eq_top (F : Family U π) [Epi π] :
    imageSubobject F.toTarget = (⊤ : Subobject N) := by
  classical
  by_contra h
  let i := equivShrink (Subobject N) (imageSubobject F.toTarget)
  have hi : subobjectAt i = imageSubobject F.toTarget :=
    (equivShrink (Subobject N)).symm_apply_apply _
  apply F.not_factors i (hi ▸ h)
  rw [hi, pullback_factors_iff]
  apply (Subobject.factors_iff _ _).mpr
  exact ⟨F.componentLift i ≫ factorThruImageSubobject F.toTarget, by
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun a ↦ F.componentLift i ≫ a)
        (imageSubobject_arrow_comp F.toTarget)).trans (F.componentLift_toTarget i))⟩

/-- The refinement subobject still maps epimorphically onto `N`. -/
@[stacks 079J "refinement epimorphism"]
theorem epi_toTarget (F : Family U π) [Epi π] : Epi F.toTarget :=
  epi_of_imageSubobject_eq_top _ F.image_toTarget_eq_top

/-- The assembled coproduct map followed by the original epimorphism is epic.  This is the
presentation-level form of `epi_toTarget`, before replacing the coproduct map by its image. -/
@[stacks 079J "coproduct map to the target is epic"]
theorem epi_map_comp (F : Family U π) [Epi π] : Epi (F.map ≫ π) := by
  rw [← F.toRefinement_toTarget]
  exact epi_comp' (inferInstanceAs (Epi (factorThruImageSubobject F.map))) F.epi_toTarget

/-- The refinement has no more subobjects than the shrink-indexed coproduct from which it is
constructed. -/
@[stacks 079J "refinement cardinal bound"]
theorem cardinalMk_refinement_le (F : Family U π) :
    Cardinal.mk (Subobject (F.refinement : C)) ≤ familyBound (U := U) (N := N) :=
  Subobject.cardinalMk_image_le F.map

end Construction

end Family

section Existence

variable [Small.{w} (Subobject N)]
variable [HasCoproduct fun _ : Shrink.{w} (Subobject N) ↦ U]

/-- A separator and an epimorphism admit a bounded refinement subobject under only the smallness
and coproduct assumptions used by the construction. -/
theorem exists_refinement (hU : IsSeparator U) (π : M ⟶ N) [Epi π] :
    ∃ P : Subobject M,
        Epi (P.arrow ≫ π) ∧
        Cardinal.mk (Subobject (P : C)) ≤ familyBound (U := U) (N := N) :=
  ⟨(Family.ofSeparator hU π).refinement, (Family.ofSeparator hU π).epi_toTarget,
    (Family.ofSeparator hU π).cardinalMk_refinement_le⟩

end Existence

section IdentityTarget

variable [Small.{w} (Subobject M)]
variable [HasCoproduct fun _ : Shrink.{w} (Subobject M) ↦ U]

/-- For the identity epimorphism of `M`, the assembled separator-family map itself is epic. -/
@[stacks 079E "separator coproduct map is epic"]
theorem Family.epi_map_of_identity (F : Family U (𝟙 M)) : Epi F.map := by
  simpa only [Category.comp_id] using F.epi_map_comp

/-- A separator supplies a small-indexed family whose assembled coproduct map is an
epimorphism onto `M`.  The selected family remains existential rather than a public choice. -/
@[stacks 079E "separator coproduct presentation"]
theorem exists_epi_map_of_isSeparator (hU : IsSeparator U) :
    ∃ F : Family U (𝟙 M), Epi F.map :=
  ⟨Family.ofSeparator hU (𝟙 M), (Family.ofSeparator hU (𝟙 M)).epi_map_of_identity⟩

end IdentityTarget

end CategoryTheory.SeparatorEpi
