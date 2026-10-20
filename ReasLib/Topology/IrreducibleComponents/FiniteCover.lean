module

public import Mathlib.Data.Set.Card
public import Mathlib.Topology.Irreducible
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite Covers by Irreducible Components

This module provides finite-cover recognition and component-count comparison
theorems for irreducible components.

@stack 0G2Y
@stack 0GM2
-/

@[expose] public section

universe u v

open Set

variable {X : Type u} [TopologicalSpace X]

/-- Lemma 5.8.4: a finite irredundant cover by closed irreducible subsets is exactly the set of
irreducible components. -/
@[stacks 0G2Y]
theorem irreducibleComponents_eq_of_finite_irreducible_closed_cover
    (S : Set (Set X)) (hS : S.Finite) (hcover : ⋃₀ S = (univ : Set X))
    (hclosed : ∀ Z ∈ S, IsClosed Z) (hirreducible : ∀ Z ∈ S, IsIrreducible Z)
    (hirredundant : ∀ Z ∈ S, ¬ Z ⊆ ⋃₀ (S \ {Z})) :
    irreducibleComponents X = S := by
  apply Set.Subset.antisymm
  · intro Z hZ
    have hZcover : Z ⊆ ⋃₀ S := by
      rw [hcover]
      exact subset_univ Z
    obtain ⟨W, hWS, hZW⟩ :=
      isIrreducible_iff_sUnion_isClosed.mp hZ.1 hS.toFinset
        (fun W hW ↦ hclosed W (hS.mem_toFinset.mp hW))
        (hS.coe_toFinset.symm ▸ hZcover)
    rw [hS.mem_toFinset] at hWS
    rw [hZ.eq_of_subset (hirreducible W hWS) hZW]
    exact hWS
  · intro Z hZS
    refine ⟨hirreducible Z hZS, ?_⟩
    intro W hW hZW
    have hWcover : W ⊆ ⋃₀ S := by
      rw [hcover]
      exact subset_univ W
    obtain ⟨V, hVS, hWV⟩ :=
      isIrreducible_iff_sUnion_isClosed.mp hW hS.toFinset
        (fun V hV ↦ hclosed V (hS.mem_toFinset.mp hV))
        (hS.coe_toFinset.symm ▸ hWcover)
    rw [hS.mem_toFinset] at hVS
    have hVZ : V = Z := by
      by_contra hVZ
      exact hirredundant Z hZS
        (hZW.trans <| hWV.trans <| subset_sUnion_of_mem ⟨hVS, by simpa using hVZ⟩)
    simpa [hVZ] using hWV

variable {Y : Type v} [TopologicalSpace Y] {f : X → Y}

/-- A continuous surjection from a space with finitely many irreducible components cannot
increase their extended cardinality. -/
theorem irreducibleComponents_encard_le_of_surjective_continuous
    (hcomponents : (irreducibleComponents X).Finite)
    (hf_surj : Function.Surjective f) (hf_cont : Continuous f) :
    (irreducibleComponents Y).encard ≤ (irreducibleComponents X).encard := by
  classical
  have hexists (C : irreducibleComponents X) :
      ∃ U ∈ irreducibleComponents Y, closure (f '' (C : Set X)) ⊆ U :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible _
      (C.property.1.image f hf_cont.continuousOn).closure
  let g : irreducibleComponents X → Set Y := fun C ↦ Classical.choose (hexists C)
  have hg_mem (C : irreducibleComponents X) :
      g C ∈ irreducibleComponents Y :=
    (Classical.choose_spec (hexists C)).1
  have hg_sub (C : irreducibleComponents X) :
      closure (f '' (C : Set X)) ⊆ g C :=
    (Classical.choose_spec (hexists C)).2
  let U : Set (Set Y) :=
    (fun C : Set X ↦ closure (f '' C)) '' irreducibleComponents X
  have hUfinite : U.Finite := hcomponents.image _
  have hUcover : ⋃₀ U = (univ : Set Y) := by
    apply eq_univ_of_forall
    intro y
    obtain ⟨x, rfl⟩ := hf_surj y
    have hx : x ∈ ⋃₀ irreducibleComponents X := by
      rw [sUnion_irreducibleComponents]
      exact mem_univ x
    obtain ⟨C, hC, hxC⟩ := mem_sUnion.mp hx
    exact mem_sUnion_of_mem (subset_closure (mem_image_of_mem f hxC)) ⟨C, hC, rfl⟩
  have hUclosed : ∀ V ∈ U, IsClosed V := by
    rintro V ⟨C, hC, rfl⟩
    exact isClosed_closure
  have htarget : irreducibleComponents Y ⊆ Set.range g := by
    intro Z hZ
    have hZcover : Z ⊆ ⋃₀ U := by
      rw [hUcover]
      exact subset_univ Z
    obtain ⟨V, hV, hZV⟩ :=
      isIrreducible_iff_sUnion_isClosed.mp hZ.1 hUfinite.toFinset
        (fun V hV ↦ hUclosed V (hUfinite.mem_toFinset.mp hV))
        (hUfinite.coe_toFinset.symm ▸ hZcover)
    rw [hUfinite.mem_toFinset] at hV
    rcases hV with ⟨C, hC, rfl⟩
    let C' : irreducibleComponents X := ⟨C, hC⟩
    refine ⟨C', ?_⟩
    exact (hZ.eq_of_subset (hg_mem C').1 (hZV.trans (hg_sub C'))).symm
  calc
    (irreducibleComponents Y).encard ≤ (Set.range g).encard :=
      Set.encard_mono htarget
    _ ≤ (Set.univ : Set (irreducibleComponents X)).encard := by
      rw [← Set.image_univ]
      exact Set.encard_image_le g _
    _ = (irreducibleComponents X).encard := by simp

/-- Lemma 5.8.5: a surjective continuous map sends a space with exactly `n` irreducible
components to a space with at most `n` irreducible components. -/
@[stacks 0GM2]
theorem irreducibleComponents_encard_le_of_surjective_continuous_of_encard_eq
    (hf_surj : Function.Surjective f) (hf_cont : Continuous f) {n : ℕ}
    (hX : (irreducibleComponents X).encard = n) :
    (irreducibleComponents Y).encard ≤ n := by
  have hcomponents : (irreducibleComponents X).Finite :=
    Set.finite_of_encard_eq_coe hX
  simpa only [hX] using
    irreducibleComponents_encard_le_of_surjective_continuous
      hcomponents hf_surj hf_cont
