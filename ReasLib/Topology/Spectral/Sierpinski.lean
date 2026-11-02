/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.ContinuousMap.T0Sierpinski
public import ReasLib.Topology.ConstructibleTopology.Maps
public import ReasLib.Topology.Spectral.Subspace

/-!
# Compact-Open Sierpinski Representations

The compact-open membership map is the canonical representation of a
prespectral space in a product of Sierpinski spaces.
-/

@[expose] public section

universe u

open Set TopologicalSpace Topology

namespace TopologicalSpace

/-- The compact-open membership map is continuous. -/
theorem continuous_compactOpenMembershipMap
    (X : Type u) [TopologicalSpace X] :
    Continuous fun x : X ↦ fun U : CompactOpens X ↦ x ∈ (U : Set X) := by
  exact continuous_pi_iff.2 fun U ↦ continuous_Prop.2 U.isOpen

/-- Lemma 5.23.13: the canonical map from a space to the Sierpinski product
indexed by its compact open subsets. -/
@[stacks 09XW "compact-open Sierpinski representation"]
def compactOpenMembershipMap
    (X : Type u) [TopologicalSpace X] : C(X, CompactOpens X → Prop) :=
  ⟨fun x U ↦ x ∈ (U : Set X), continuous_compactOpenMembershipMap X⟩

/-- Evaluation of the compact-open membership map is membership in the compact
open subset. -/
@[simp]
theorem compactOpenMembershipMap_apply
    (X : Type u) [TopologicalSpace X] (x : X) (U : CompactOpens X) :
    compactOpenMembershipMap X x U ↔ x ∈ (U : Set X) := Iff.rfl

/-- When compact opens form a basis, the compact-open membership map is
inducing. -/
theorem compactOpenMembershipMap_isInducing
    (X : Type u) [TopologicalSpace X] [PrespectralSpace X] :
    IsInducing (compactOpenMembershipMap X) := by
  refine ⟨le_antisymm (compactOpenMembershipMap X).continuous.le_induced ?_⟩
  intro s hs
  obtain ⟨S, hS, rfl⟩ := PrespectralSpace.isTopologicalBasis.open_eq_sUnion hs
  refine @isOpen_sUnion X (induced (compactOpenMembershipMap X) inferInstance) S ?_
  intro U hU
  let V : CompactOpens X := ⟨⟨U, (hS hU).2⟩, (hS hU).1⟩
  refine isOpen_induced_iff.mpr
    ⟨{p | p V}, continuous_Prop.mp (continuous_apply V), ?_⟩
  rfl

/-- In a `T₀` prespectral space, compact-open membership separates points. -/
theorem compactOpenMembershipMap_injective
    (X : Type u) [TopologicalSpace X] [PrespectralSpace X] [T0Space X] :
    Function.Injective (compactOpenMembershipMap X) := by
  exact (compactOpenMembershipMap_isInducing X).injective

/-- In a `T₀` prespectral space, the compact-open membership map is an
embedding. -/
theorem compactOpenMembershipMap_isEmbedding
    (X : Type u) [TopologicalSpace X] [PrespectralSpace X] [T0Space X] :
    IsEmbedding (compactOpenMembershipMap X) :=
  ⟨compactOpenMembershipMap_isInducing X, compactOpenMembershipMap_injective X⟩

/-- For a spectral space, the compact-open membership map is spectral. -/
theorem compactOpenMembershipMap_isSpectralMap
    (X : Type u) [TopologicalSpace X] [SpectralSpace X] :
    IsSpectralMap (compactOpenMembershipMap X) := by
  classical
  have hcoord (U : CompactOpens X) (s : Set Prop) (hs : IsOpen s) :
      IsCompact ((fun x : X ↦ x ∈ (U : Set X)) ⁻¹' s) := by
    by_cases hfalse : False ∈ s
    · have hs' : s = univ := by
        simpa only [nhds_false, Filter.mem_top] using hs.mem_nhds hfalse
      simpa [hs'] using (isCompact_univ : IsCompact (univ : Set X))
    · by_cases htrue : True ∈ s
      · have hs' : s = {True} := by
          ext p
          by_cases hp : p <;> simp_all
        simpa [hs'] using U.isCompact
      · have hs' : s = ∅ := by
          ext p
          by_cases hp : p <;> simp_all
        simpa [hs'] using (isCompact_empty : IsCompact (∅ : Set X))
  let B : Set (Set (CompactOpens X → Prop)) :=
    {s | ∃ (U : CompactOpens X → Set Prop) (F : Finset (CompactOpens X)),
      (∀ i, i ∈ F → IsOpen (U i)) ∧ s = (F : Set (CompactOpens X)).pi U}
  have hB : IsTopologicalBasis B :=
    isTopologicalBasis_pi fun _ ↦ isTopologicalBasis_opens
  have hpre (s : B) : IsCompact (compactOpenMembershipMap X ⁻¹' (s : Set _)) := by
    obtain ⟨s, U, F, hU, rfl⟩ := s
    let V : CompactOpens X → Set X := fun i ↦
      (fun x : X ↦ x ∈ (i : Set X)) ⁻¹' U i
    have heq : compactOpenMembershipMap X ⁻¹' (F : Set (CompactOpens X)).pi U =
        ⋂₀ (V '' (F : Set (CompactOpens X))) := by
      ext x
      simp [V, Set.mem_pi, compactOpenMembershipMap]
    rw [heq]
    refine QuasiSeparatedSpace.isCompact_sInter (F.finite_toSet.image V) ?_ ?_
    · rintro _ ⟨i, hi, rfl⟩
      exact Or.inl ((hU i hi).preimage (continuous_Prop.2 i.isOpen))
    · rintro _ ⟨i, hi, rfl⟩
      exact hcoord i (U i) (hU i hi)
  refine ⟨(compactOpenMembershipMap X).continuous, fun s hs hc ↦ ?_⟩
  obtain ⟨S, hS, rfl⟩ :=
    eq_finite_iUnion_of_isTopologicalBasis_of_isCompact_open
      (fun s : B ↦ (s : Set (CompactOpens X → Prop))) (by simpa using hB) s hc hs
  simpa only [Set.preimage_iUnion] using hS.isCompact_biUnion fun s _ ↦ hpre s

/-- The range of the compact-open membership map of a spectral space is closed
in the constructible topology of its Sierpinski product. -/
theorem isClosed_range_compactOpenMembershipMap_constructibleTopology
    (X : Type u) [TopologicalSpace X] [SpectralSpace X] :
    IsClosed[constructibleTopology (CompactOpens X → Prop)]
      (Set.range (compactOpenMembershipMap X)) := by
  classical
  let Y := CompactOpens X → Prop
  let C : CompactOpens X → Set Y := fun i ↦ {p | p i}
  have hCo (i : CompactOpens X) : IsOpen (C i) :=
    continuous_Prop.mp (continuous_apply i)
  have hCc (i : CompactOpens X) : IsCompact (C i) := by
    convert isCompact_pi_infinite (s := fun j : CompactOpens X ↦ {q : Prop | j = i → q})
      (fun _ ↦ (Set.toFinite _).isCompact) using 1
    ext p
    change p i ↔ ∀ j, j = i → p j
    constructor
    · intro hp j hji
      simpa [hji] using hp
    · intro hp
      exact hp i rfl
  let D : CompactOpens X → Set (WithConstructibleTopology Y) :=
    fun i ↦ WithTopology.ofTopology ⁻¹' C i
  have hC (i : CompactOpens X) : IsClopen (D i) := by
    constructor
    · apply WithConstructibleTopology.isClosed_iff.mpr
      refine @IsClosed.mk Y (constructibleTopology Y) (C i) ?_
      exact .basic _ (Or.inr ⟨(hCo i).isClosed_compl, by simpa using hCc i⟩)
    · apply WithConstructibleTopology.isOpen_iff.mpr
      exact (hCc i).isOpen_constructibleTopology_of_isOpen (hCo i)
  letI : T2Space (WithConstructibleTopology Y) := by
    constructor
    intro f g hfg
    have hne : (WithTopology.ofTopology f : Y) ≠ WithTopology.ofTopology g :=
      fun h ↦ hfg (WithTopology.ofTopology_injective _ h)
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    by_cases hf : WithTopology.ofTopology f i
    · have hg : ¬WithTopology.ofTopology g i :=
        fun hg ↦ hi (propext ⟨fun _ ↦ hg, fun _ ↦ hf⟩)
      exact ⟨D i, (D i)ᶜ, (hC i).isOpen, (hC i).isClosed.isOpen_compl,
        hf, hg, disjoint_compl_right⟩
    · have hg : WithTopology.ofTopology g i := by
        by_contra hg
        exact hi (propext (by simp [hf, hg]))
      exact ⟨(D i)ᶜ, D i, (hC i).isClosed.isOpen_compl, (hC i).isOpen,
        hf, hg, disjoint_compl_left⟩
  have hf : Continuous[constructibleTopology X, constructibleTopology Y]
      (compactOpenMembershipMap X) := by
    apply continuous_generateFrom_iff.mpr
    rintro s (⟨ho, hc⟩ | ⟨hcl, hcc⟩)
    · have hc' := (compactOpenMembershipMap_isSpectralMap X).isCompact_preimage_of_isOpen ho hc
      exact hc'.isOpen_constructibleTopology_of_isOpen
        (ho.preimage (compactOpenMembershipMap X).continuous)
    · exact ((compactOpenMembershipMap_isSpectralMap X).isCompact_preimage_of_isOpen
        hcl.isOpen_compl hcc).isOpen_constructibleTopology_of_isClosed
          (hcl.preimage (compactOpenMembershipMap X).continuous)
  let f : WithConstructibleTopology X → WithConstructibleTopology Y := fun x ↦
    WithTopology.toTopology (constructibleTopology Y)
      (compactOpenMembershipMap X (WithTopology.ofTopology x))
  have hf' : Continuous[_, constructibleTopology Y]
      (fun x : WithConstructibleTopology X ↦
        compactOpenMembershipMap X (WithTopology.ofTopology x)) :=
    @Continuous.comp _ _ _ _ (constructibleTopology X) (constructibleTopology Y) _ _
      hf (WithTopology.continuous_ofTopology _)
  have hfc : Continuous f :=
    @Continuous.comp _ _ _ _ (constructibleTopology Y) _ _ _
      (WithTopology.continuous_toTopology _) hf'
  have heq : WithTopology.toTopology (constructibleTopology Y) ⁻¹' range f =
      range (compactOpenMembershipMap X) := by
    ext p
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨WithTopology.ofTopology x, WithTopology.toTopology_injective _ hx⟩
    · rintro ⟨x, rfl⟩
      exact ⟨WithTopology.toTopology (constructibleTopology X) x, rfl⟩
  rw [← heq]
  exact WithConstructibleTopology.isClosed_iff.mp (isCompact_range hfc).isClosed

end TopologicalSpace

namespace SpectralSpace

/-- Lemma 5.23.13: a topological space is spectral exactly when it is
homeomorphic to a constructibly closed subspace of a Sierpinski product. -/
@[stacks 09XW]
theorem iff_homeomorphic_constructiblyClosed_sierpinskiProduct
    (X : Type u) [TopologicalSpace X] :
    SpectralSpace X ↔
      ∃ (ι : Type u) (E : Set (ι → Prop)),
        IsClosed[constructibleTopology (ι → Prop)] E ∧ Nonempty (X ≃ₜ E) := by
  constructor
  · intro hX
    letI := hX
    exact ⟨TopologicalSpace.CompactOpens X, range (TopologicalSpace.compactOpenMembershipMap X),
      TopologicalSpace.isClosed_range_compactOpenMembershipMap_constructibleTopology X,
      ⟨(TopologicalSpace.compactOpenMembershipMap_isEmbedding X).toHomeomorph⟩⟩
  · sorry

end SpectralSpace
