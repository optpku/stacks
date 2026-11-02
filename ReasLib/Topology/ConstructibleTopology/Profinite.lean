/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Category.Profinite.Basic
public import ReasLib.Topology.Category.Profinite.Recognition
public import ReasLib.Topology.ConstructibleTopology.Specialization

/-!
# Profinite Criteria for Spectral Spaces

This module packages the equivalent separation, specialization, and
constructible-topology criteria for a spectral space to be profinite.
-/

@[expose] public section

universe u

open Set TopologicalSpace Topology

namespace SpectralSpace

private theorem isClosed_constructible_of_isOpen_isCompact {X : Type u}
    [TopologicalSpace X] {U : Set X} (hUo : IsOpen U) (hUc : IsCompact U) :
    IsClosed[constructibleTopology X] U := by
  apply (@isOpen_compl_iff X U (constructibleTopology X)).mp
  exact (show IsCompact (Uᶜ)ᶜ by simpa using hUc).isOpen_constructibleTopology_of_isClosed
    hUo.isClosed_compl

/-- Patch compactness makes a compact open closed once all specializations are trivial. -/
private theorem t2Space_of_t1Space {X : Type u} [TopologicalSpace X]
    [SpectralSpace X] [T1Space X] : T2Space X := by
  have hpatch : @CompactSpace X (constructibleTopology X) :=
    @Function.Surjective.compactSpace (WithConstructibleTopology X) X
      inferInstance (constructibleTopology X) _ (WithTopology.continuous_ofTopology _) inferInstance
      (WithTopology.ofTopology_surjective _)
  have hclosed : ∀ U : Set X, IsOpen U → IsCompact U → IsClosed U := by
    intro U hUo hUc
    apply isClosed_of_closure_subset
    intro x hx
    let N := { V : Set X // IsOpen V ∧ IsCompact V ∧ x ∈ V }
    have hUpatch : @IsCompact X (constructibleTopology X) U :=
      @IsClosed.isCompact X (constructibleTopology X) U hpatch
        (isClosed_constructible_of_isOpen_isCompact hUo hUc)
    obtain ⟨y, hyU, hyN⟩ := @IsCompact.inter_iInter_nonempty X (constructibleTopology X) U N
      hUpatch (fun V : N ↦ (V : Set X))
      (fun V ↦ isClosed_constructible_of_isOpen_isCompact V.2.1 V.2.2.1) (by
        intro s
        have ho : IsOpen (⋂ V ∈ s, (V : Set X)) :=
          isOpen_biInter_finset fun V _ ↦ V.2.1
        have hxN : x ∈ ⋂ V ∈ s, (V : Set X) := by
          simp only [Set.mem_iInter]
          exact fun V _ ↦ V.2.2.2
        simpa only [Set.inter_comm] using mem_closure_iff.mp hx _ ho hxN)
    have hyx : y ⤳ x := by
      apply specializes_iff_forall_open.mpr
      intro V hVo hxV
      obtain ⟨W, ⟨hWo, hWc⟩, hxW, hWV⟩ :=
        PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hxV hVo
      exact hWV (Set.mem_iInter.mp hyN ⟨W, hWo, hWc, hxW⟩)
    exact hyx.eq ▸ hyU
  haveI : TotallySeparatedSpace X := totallySeparatedSpace_iff_exists_isClopen.mpr <| by
    intro x y hxy
    obtain ⟨U, ⟨hUo, hUc⟩, hxU, hyU⟩ :=
      PrespectralSpace.isTopologicalBasis.exists_mem_of_ne hxy
    exact ⟨U, ⟨hclosed U hUo hUc, hUo⟩, hxU, hyU⟩
  infer_instance

/-- A spectral space has a profinite model exactly when it is Hausdorff. -/
@[stacks 0905 "profinite iff Hausdorff"]
theorem profinite_iff_t2Space (X : Type u) [TopologicalSpace X] [SpectralSpace X] :
    (∃ P : Profinite.{u}, Nonempty (X ≃ₜ P)) ↔ T2Space X := by
  constructor
  · rintro ⟨P, ⟨e⟩⟩
    exact e.symm.t2Space
  · intro h
    letI := h
    exact ⟨Profinite.of X, ⟨Homeomorph.refl X⟩⟩

/-- For a spectral space, Hausdorffness is equivalent to total
disconnectedness. -/
@[stacks 0905 "Hausdorff iff totally disconnected"]
theorem t2Space_iff_totallyDisconnectedSpace (X : Type u) [TopologicalSpace X]
    [SpectralSpace X] :
    T2Space X ↔ TotallyDisconnectedSpace X := by
  constructor
  · intro h
    letI := h
    infer_instance
  · intro h
    letI := h
    haveI : T1Space X := ⟨fun x ↦ by
      rw [← connectedComponent_eq_singleton x]
      exact isClosed_connectedComponent⟩
    exact t2Space_of_t1Space

/-- For a spectral space, Hausdorffness is equivalent to every open compact
subset being closed. -/
@[stacks 0905 "Hausdorff iff open compact subsets are closed"]
theorem t2Space_iff_forall_isOpen_isCompact_isClosed (X : Type u) [TopologicalSpace X]
    [SpectralSpace X] :
    T2Space X ↔ ∀ U : Set X, IsOpen U → IsCompact U → IsClosed U := by
  constructor
  · intro h
    letI := h
    exact fun _ _ hUc ↦ hUc.isClosed
  · intro h
    haveI : T1Space X := t1Space_iff_specializes_imp_eq.mpr <| by
      intro x y hxy
      apply PrespectralSpace.isTopologicalBasis.eq_iff.mpr
      intro U hU
      exact ⟨hxy.mem_closed (h U hU.1 hU.2), hxy.mem_open hU.1⟩
    exact t2Space_of_t1Space

/-- For a spectral space, Hausdorffness is equivalent to triviality of the
specialization relation. -/
@[stacks 0905 "Hausdorff iff specialization is trivial"]
theorem t2Space_iff_specializes_imp_eq (X : Type u) [TopologicalSpace X]
    [SpectralSpace X] :
    T2Space X ↔ ∀ ⦃x y : X⦄, x ⤳ y → x = y := by
  constructor
  · intro h
    letI := h
    exact fun _ _ hxy ↦ hxy.eq
  · intro h
    haveI : T1Space X := t1Space_iff_specializes_imp_eq.mpr h
    exact t2Space_of_t1Space

/-- For a spectral space, Hausdorffness is equivalent to every singleton
being closed. -/
@[stacks 0905 "Hausdorff iff points are closed"]
theorem t2Space_iff_isClosed_singleton (X : Type u) [TopologicalSpace X]
    [SpectralSpace X] :
    T2Space X ↔ ∀ x : X, IsClosed ({x} : Set X) := by
  constructor
  · intro h
    letI := h
    exact fun _ ↦ isClosed_singleton
  · intro h
    haveI : T1Space X := ⟨h⟩
    exact t2Space_of_t1Space

/-- For a spectral space, Hausdorffness is equivalent to each point being the
generic point of its irreducible component. -/
@[stacks 0905 "Hausdorff iff irreducible-component points are generic"]
theorem t2Space_iff_isGenericPoint_irreducibleComponent (X : Type u)
    [TopologicalSpace X] [SpectralSpace X] :
    T2Space X ↔ ∀ x : X, IsGenericPoint x (irreducibleComponent x) := by
  constructor
  · intro h
    letI := h
    intro x
    rw [isGenericPoint_def, closure_singleton]
    apply Set.Subset.antisymm (Set.singleton_subset_iff.mpr mem_irreducibleComponent)
    intro y hy
    exact Set.mem_singleton_iff.mpr
      (isIrreducible_irreducibleComponent.isPreirreducible.subsingleton hy
        mem_irreducibleComponent)
  · intro h
    apply (t2Space_iff_specializes_imp_eq X).mpr
    intro x y hxy
    have hsub : irreducibleComponent y ⊆ irreducibleComponent x := by
      rw [← (h y).def, ← (h x).def]
      exact hxy.closure_subset
    have heq : irreducibleComponent x = irreducibleComponent y :=
      eq_irreducibleComponent isIrreducible_irreducibleComponent.isPreirreducible hsub
    apply (h x).eq
    exact (h y).def.trans heq.symm

/-- For a spectral space, Hausdorffness is equivalent to the constructible
topology agreeing with the original topology. -/
@[stacks 0905 "Hausdorff iff patch topology is original"]
theorem t2Space_iff_constructibleTopology_eq (X : Type u) [TopologicalSpace X]
    [SpectralSpace X] :
    T2Space X ↔ constructibleTopology X = ‹TopologicalSpace X› := by
  constructor
  · intro h
    letI := h
    apply le_antisymm
    · conv_rhs => rw [(PrespectralSpace.isTopologicalBasis (X := X)).eq_generateFrom]
      exact generateFrom_anti fun _ hU ↦ Or.inl hU
    · apply le_generateFrom
      rintro U (hU | hU)
      · exact hU.1
      · simpa using hU.2.isClosed.isOpen_compl
  · intro h
    apply (t2Space_iff_forall_isOpen_isCompact_isClosed X).mpr
    intro U hUo hUc
    have hU := isClosed_constructible_of_isOpen_isCompact hUo hUc
    rwa [h] at hU

/-- Lemma 5.23.8: the standard profinite, separation, specialization, and
constructible-topology criteria for a spectral space are equivalent. -/
@[stacks 0905]
theorem profinite_criteria (X : Type u) [TopologicalSpace X] [SpectralSpace X] :
    List.TFAE
      [ ∃ P : Profinite.{u}, Nonempty (X ≃ₜ P),
        T2Space X,
        TotallyDisconnectedSpace X,
        ∀ U : Set X, IsOpen U → IsCompact U → IsClosed U,
        ∀ ⦃x y : X⦄, x ⤳ y → x = y,
        ∀ x : X, IsClosed ({x} : Set X),
        ∀ x : X, IsGenericPoint x (irreducibleComponent x),
        constructibleTopology X = ‹TopologicalSpace X› ] := by
  apply List.tfae_of_forall (T2Space X)
  intro P hP
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profinite_iff_t2Space X
  · exact Iff.rfl
  · exact (t2Space_iff_totallyDisconnectedSpace X).symm
  · exact (t2Space_iff_forall_isOpen_isCompact_isClosed X).symm
  · exact (t2Space_iff_specializes_imp_eq X).symm
  · exact (t2Space_iff_isClosed_singleton X).symm
  · exact (t2Space_iff_isGenericPoint_irreducibleComponent X).symm
  · exact (t2Space_iff_constructibleTopology_eq X).symm

end SpectralSpace
