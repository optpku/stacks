module

public import ReasLib.Topology.Spectral.Limit.Constructible
public import ReasLib.Topology.Spectral.Limit.Eventual

/-!
# Compact open subsets of spectral inverse limits

This module gives descent and eventual-equality results for compact open subsets of cofiltered
limits of spectral spaces.
-/

@[expose] public section

universe u v w

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits

section

variable {J : Type v} [Category.{w} J] [IsCofiltered J]
variable {F : J ⥤ TopCat.{max v w}} [∀ j : J, SpectralSpace (F.obj j)]

/-- Every compact open subset of a cofiltered spectral limit is pulled back from a compact open
subset at one stage. -/
@[stacks 0A30 "compact opens descend"]
theorem compact_open_eq_preimage_of_limit
    (hF : ∀ ⦃i j : J⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    (U : CompactOpens (limit F : TopCat)) :
    ∃ (i : J) (Ui : CompactOpens (F.obj i)),
      (U : Set (limit F : TopCat)) = (limit.π F i) ⁻¹' (Ui : Set (F.obj i)) := sorry

/-- An inclusion between pullbacks of compact opens holds after pullback to one common refinement
stage. -/
@[stacks 0A30 "compact-open inclusions descend"]
theorem exists_common_refinement_of_preimage_subset
    (hF : ∀ ⦃i j : J⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i j : J} (Ui : CompactOpens (F.obj i)) (Uj : CompactOpens (F.obj j))
    (hsub : (limit.π F i) ⁻¹' (Ui : Set (F.obj i)) ⊆
      (limit.π F j) ⁻¹' (Uj : Set (F.obj j))) :
    ∃ (k : J) (a : k ⟶ i) (b : k ⟶ j),
      (F.map a) ⁻¹' (Ui : Set (F.obj i)) ⊆
        (F.map b) ⁻¹' (Uj : Set (F.obj j)) := sorry

/-- A finite union identity between pullbacks of compact opens holds after one transition to the
chosen stage. -/
@[stacks 0A30 "compact-open finite unions descend"]
theorem exists_stage_of_preimage_eq_iUnion
    (hF : ∀ ⦃i j : J⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i : J} {ι : Type u} [Finite ι] (Ui : CompactOpens (F.obj i))
    (V : ι → CompactOpens (F.obj i))
    (hcover : (limit.π F i) ⁻¹' (Ui : Set (F.obj i)) =
      ⋃ t, (limit.π F i) ⁻¹' (V t : Set (F.obj i))) :
    ∃ (j : J) (a : j ⟶ i),
      (F.map a) ⁻¹' (Ui : Set (F.obj i)) =
        ⋃ t, (F.map a) ⁻¹' (V t : Set (F.obj i)) := sorry

/-- A finite intersection identity between pullbacks of compact opens holds after one transition
to the chosen stage. -/
@[stacks 0A30 "compact-open finite intersections descend"]
theorem exists_stage_of_preimage_eq_iInter
    (hF : ∀ ⦃i j : J⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {i : J} {ι : Type u} [Finite ι] (Ui : CompactOpens (F.obj i))
    (V : ι → CompactOpens (F.obj i))
    (hcover : (limit.π F i) ⁻¹' (Ui : Set (F.obj i)) =
      ⋂ t, (limit.π F i) ⁻¹' (V t : Set (F.obj i))) :
    ∃ (j : J) (a : j ⟶ i),
      (F.map a) ⁻¹' (Ui : Set (F.obj i)) =
        ⋂ t, (F.map a) ⁻¹' (V t : Set (F.obj i)) := sorry

end
