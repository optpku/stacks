/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalSpectrum.GlobalSections

@[expose] public section

universe u

noncomputable section

open CategoryTheory Opposite TopCat Topology TopologicalSpace

namespace AlgebraicGeometry.FormalSpectrum

variable {A B : Type u} [CommRing A] [TopologicalSpace A]
  [TopologicalRing.IsAdmissibleRing A] [CommRing B] [TopologicalSpace B]
  [TopologicalRing.IsAdmissibleRing B]

/-- The continuous map on open primes induced contravariantly by a continuous ring map. -/
def mapBase (φ : A →+* B) (hφ : Continuous φ) :
    TopCat.of (OpenPrime B) ⟶ TopCat.of (OpenPrime A) :=
  TopCat.ofHom ⟨OpenPrime.comap φ hφ, OpenPrime.continuous_comap φ hφ⟩

/-- The corresponding target open lies in the inverse image under the induced quotient map. -/
theorem pullbackOpens_subset_comap_quotient (φ : A →+* B) (hφ : Continuous φ)
    (U : Opens (OpenPrime A)) {I : Ideal A} {J : Ideal B}
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hJ : TopologicalRing.Ideal.IsIdealOfDefinition J) (hIJ : I ≤ Ideal.comap φ J) :
    (pullbackOpens (Opens.comap (mapBase φ hφ).hom U) J hJ : Set (PrimeSpectrum (B ⧸ J))) ⊆
      PrimeSpectrum.comap (Ideal.quotientMap J φ hIJ) ⁻¹' pullbackOpens U I hI := by
  intro q hq
  change OpenPrime.homeomorphQuotientInv I hI
    (PrimeSpectrum.comap (Ideal.quotientMap J φ hIJ) q) ∈ U
  change OpenPrime.comap φ hφ (OpenPrime.homeomorphQuotientInv J hJ q) ∈ U at hq
  have h : OpenPrime.homeomorphQuotientInv I hI
      (PrimeSpectrum.comap (Ideal.quotientMap J φ hIJ) q) =
        OpenPrime.comap φ hφ (OpenPrime.homeomorphQuotientInv J hJ q) := by
    apply Subtype.ext
    change PrimeSpectrum.comap (Ideal.Quotient.mk I)
      (PrimeSpectrum.comap (Ideal.quotientMap J φ hIJ) q) =
        PrimeSpectrum.comap φ (PrimeSpectrum.comap (Ideal.Quotient.mk J) q)
    rw [← PrimeSpectrum.comap_comp_apply, Ideal.quotientMap_comp_mk,
      PrimeSpectrum.comap_comp_apply]
  rwa [h]

/-- The component section map induced by a homomorphism between the quotient rings. -/
def componentMapOfLe (φ : A →+* B) (hφ : Continuous φ) (U : Opens (OpenPrime A))
    {I : Ideal A} {J : Ideal B} (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hJ : TopologicalRing.Ideal.IsIdealOfDefinition J) (hIJ : I ≤ Ideal.comap φ J) :
    componentType U I hI →+* componentType (Opens.comap (mapBase φ hφ).hom U) J hJ :=
  StructureSheaf.comap (Ideal.quotientMap J φ hIJ) (pullbackOpens U I hI)
    (pullbackOpens (Opens.comap (mapBase φ hφ).hom U) J hJ)
    (pullbackOpens_subset_comap_quotient φ hφ U hI hJ hIJ)

/-- The source ideal used to compute the `J`-component of the induced section map: a fixed
ideal of definition of `A` intersected with the inverse image of `J`.  The resulting component
does not depend on this choice; see `sectionsMap_apply_of_le`. -/
def sourceIdeal (φ : A →+* B) (J : Ideal B) : Ideal A :=
  (TopologicalRing.IsPreadmissibleRing.exists_ideal_isIdealOfDefinition (R := A)).choose ⊓
    Ideal.comap φ J

/-- The source ideal of an ideal of definition is an ideal of definition. -/
theorem isIdealOfDefinition_sourceIdeal (φ : A →+* B) (hφ : Continuous φ) {J : Ideal B}
    (hJ : TopologicalRing.Ideal.IsIdealOfDefinition J) :
    TopologicalRing.Ideal.IsIdealOfDefinition (sourceIdeal φ J) := by
  have hI :=
    (TopologicalRing.IsPreadmissibleRing.exists_ideal_isIdealOfDefinition (R := A)).choose_spec
  refine ⟨hI.1.inter (hJ.1.preimage hφ), ?_⟩
  intro U hU
  obtain ⟨n, hn⟩ := hI.2 U hU
  have hpow : sourceIdeal φ J ^ n ≤
      (TopologicalRing.IsPreadmissibleRing.exists_ideal_isIdealOfDefinition (R := A)).choose ^ n :=
    pow_le_pow_left' inf_le_left n
  exact ⟨n, fun x hx => hn (hpow hx)⟩

/-- The source ideal is contained in the inverse image of the target ideal. -/
theorem sourceIdeal_le_comap (φ : A →+* B) (J : Ideal B) :
    sourceIdeal φ J ≤ Ideal.comap φ J :=
  inf_le_right

/-- The inverse image of an ideal of definition contains an ideal of definition. -/
theorem exists_isIdealOfDefinition_le_comap (φ : A →+* B) (hφ : Continuous φ)
    {J : Ideal B} (hJ : TopologicalRing.Ideal.IsIdealOfDefinition J) :
    ∃ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I ∧ I ≤ Ideal.comap φ J :=
  ⟨sourceIdeal φ J, isIdealOfDefinition_sourceIdeal φ hφ hJ, sourceIdeal_le_comap φ J⟩

omit [TopologicalRing.IsAdmissibleRing A] in
private theorem isIdealOfDefinition_inf {I K : Ideal A}
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hK : TopologicalRing.Ideal.IsIdealOfDefinition K) :
    TopologicalRing.Ideal.IsIdealOfDefinition (I ⊓ K) := by
  refine ⟨hI.1.inter hK.1, ?_⟩
  intro U hU
  obtain ⟨n, hn⟩ := hI.2 U hU
  have hpow : (I ⊓ K) ^ n ≤ I ^ n := pow_le_pow_left' inf_le_left n
  exact ⟨n, fun x hx => hn (hpow hx)⟩

set_option backward.isDefEq.respectTransparency false in
private theorem componentMapOfLe_source_transition (φ : A →+* B) (hφ : Continuous φ)
    (U : Opens (OpenPrime A)) {I K : Ideal A} {J : Ideal B}
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hK : TopologicalRing.Ideal.IsIdealOfDefinition K)
    (hJ : TopologicalRing.Ideal.IsIdealOfDefinition J)
    (hIK : I ≤ K) (hKJ : K ≤ Ideal.comap φ J) :
    (componentMapOfLe φ hφ U hK hJ hKJ).comp (transition U hI hK hIK) =
      componentMapOfLe φ hφ U hI hJ (hIK.trans hKJ) := by
  have hq : (Ideal.quotientMap J φ hKJ).comp (Ideal.Quotient.factor hIK) =
      Ideal.quotientMap J φ (hIK.trans hKJ) := by
    apply Ideal.Quotient.ringHom_ext
    exact RingHom.ext fun _ => rfl
  have hc := StructureSheaf.comap_comp (Ideal.Quotient.factor hIK) (Ideal.quotientMap J φ hKJ)
    (pullbackOpens U I hI) (pullbackOpens U K hK)
    (pullbackOpens (Opens.comap (mapBase φ hφ).hom U) J hJ)
    (pullbackOpens_subset_comap_factor U hI hK hIK)
    (pullbackOpens_subset_comap_quotient φ hφ U hK hJ hKJ)
  apply RingHom.ext
  intro s
  simpa only [componentMapOfLe, transition, instCommRingComponentType, componentType, hq]
    using (RingHom.congr_fun hc s).symm

set_option backward.isDefEq.respectTransparency false in
private theorem componentMapOfLe_target_transition (φ : A →+* B) (hφ : Continuous φ)
    (U : Opens (OpenPrime A)) {I : Ideal A} {J K : Ideal B}
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hJ : TopologicalRing.Ideal.IsIdealOfDefinition J)
    (hK : TopologicalRing.Ideal.IsIdealOfDefinition K)
    (hIJ : I ≤ Ideal.comap φ J) (hJK : J ≤ K) :
    (transition (Opens.comap (mapBase φ hφ).hom U) hJ hK hJK).comp
        (componentMapOfLe φ hφ U hI hJ hIJ) =
      componentMapOfLe φ hφ U hI hK (fun _ hx => hJK (hIJ hx)) := by
  have hq : (Ideal.Quotient.factor hJK).comp (Ideal.quotientMap J φ hIJ) =
      Ideal.quotientMap K φ (fun _ hx => hJK (hIJ hx)) := by
    apply Ideal.Quotient.ringHom_ext
    exact RingHom.ext fun _ => rfl
  have hc := StructureSheaf.comap_comp (Ideal.quotientMap J φ hIJ) (Ideal.Quotient.factor hJK)
    (pullbackOpens U I hI)
    (pullbackOpens (Opens.comap (mapBase φ hφ).hom U) J hJ)
    (pullbackOpens (Opens.comap (mapBase φ hφ).hom U) K hK)
    (pullbackOpens_subset_comap_quotient φ hφ U hI hJ hIJ)
    (pullbackOpens_subset_comap_factor (Opens.comap (mapBase φ hφ).hom U) hJ hK hJK)
  apply RingHom.ext
  intro s
  simpa only [componentMapOfLe, transition, instCommRingComponentType, componentType, hq]
    using (RingHom.congr_fun hc s).symm

private theorem componentMapOfLe_eq (φ : A →+* B) (hφ : Continuous φ)
    (U : Opens (OpenPrime A)) (s : Sections U) {I K : Ideal A} {J : Ideal B}
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hK : TopologicalRing.Ideal.IsIdealOfDefinition K)
    (hJ : TopologicalRing.Ideal.IsIdealOfDefinition J)
    (hIJ : I ≤ Ideal.comap φ J) (hKJ : K ≤ Ideal.comap φ J) :
    componentMapOfLe φ hφ U hI hJ hIJ (s.component I hI) =
      componentMapOfLe φ hφ U hK hJ hKJ (s.component K hK) := by
  have hL := isIdealOfDefinition_inf hI hK
  calc
    _ = componentMapOfLe φ hφ U hI hJ hIJ
        (transition U hL hI inf_le_left (s.component (I ⊓ K) hL)) :=
      congrArg (componentMapOfLe φ hφ U hI hJ hIJ) (s.property hL hI inf_le_left).symm
    _ = componentMapOfLe φ hφ U hL hJ (inf_le_left.trans hIJ)
        (s.component (I ⊓ K) hL) :=
      RingHom.congr_fun
        (componentMapOfLe_source_transition φ hφ U hL hI hJ inf_le_left hIJ) _
    _ = componentMapOfLe φ hφ U hK hJ hKJ
        (transition U hL hK inf_le_right (s.component (I ⊓ K) hL)) :=
      (RingHom.congr_fun
        (componentMapOfLe_source_transition φ hφ U hL hK hJ inf_le_right hKJ) _).symm
    _ = _ := congrArg (componentMapOfLe φ hφ U hK hJ hKJ) (s.property hL hK inf_le_right)

/-- Each target component is uniquely determined by every eligible source quotient component. -/
theorem sectionsMapComponent_existsUnique (φ : A →+* B) (hφ : Continuous φ)
    (U : Opens (OpenPrime A)) (s : Sections U) (J : Ideal B)
    (hJ : TopologicalRing.Ideal.IsIdealOfDefinition J) :
    ∃! t : componentType (Opens.comap (mapBase φ hφ).hom U) J hJ,
      ∀ (I : Ideal A) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
        (hIJ : I ≤ Ideal.comap φ J), t = componentMapOfLe φ hφ U hI hJ hIJ (s.component I hI) := by
  refine ⟨componentMapOfLe φ hφ U (isIdealOfDefinition_sourceIdeal φ hφ hJ) hJ
    (sourceIdeal_le_comap φ J)
    (s.component (sourceIdeal φ J) (isIdealOfDefinition_sourceIdeal φ hφ hJ)), ?_, ?_⟩
  · intro I hI hIJ
    exact componentMapOfLe_eq φ hφ U s _ hI hJ _ hIJ
  · intro t ht
    exact ht (sourceIdeal φ J) (isIdealOfDefinition_sourceIdeal φ hφ hJ)
      (sourceIdeal_le_comap φ J)

/-- The `J`-component of the induced section map, computed from the component of the source
section at `sourceIdeal φ J`. -/
def mappedComponent (φ : A →+* B) (hφ : Continuous φ)
    (U : Opens (OpenPrime A)) (s : Sections U) (J : Ideal B)
    (hJ : TopologicalRing.Ideal.IsIdealOfDefinition J) :
    componentType (Opens.comap (mapBase φ hφ).hom U) J hJ :=
  componentMapOfLe φ hφ U (isIdealOfDefinition_sourceIdeal φ hφ hJ) hJ
    (sourceIdeal_le_comap φ J)
    (s.component (sourceIdeal φ J) (isIdealOfDefinition_sourceIdeal φ hφ hJ))

private theorem mappedComponent_eq (φ : A →+* B) (hφ : Continuous φ)
    (U : Opens (OpenPrime A)) (s : Sections U) {I : Ideal A} {J : Ideal B}
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hJ : TopologicalRing.Ideal.IsIdealOfDefinition J) (hIJ : I ≤ Ideal.comap φ J) :
    mappedComponent φ hφ U s J hJ =
      componentMapOfLe φ hφ U hI hJ hIJ (s.component I hI) :=
  componentMapOfLe_eq φ hφ U s _ hI hJ _ hIJ

/-- The family of target components determined by a continuous ring map. -/
def mappedFamily (φ : A →+* B) (hφ : Continuous φ) (U : Opens (OpenPrime A))
    (s : Sections U) : ComponentFamily (Opens.comap (mapBase φ hφ).hom U) :=
  fun J ↦ mappedComponent φ hφ U s J.val J.property

/-- The induced component family is compatible and preserves the ring operations. -/
theorem sectionsMap_laws (φ : A →+* B) (hφ : Continuous φ) (U : Opens (OpenPrime A)) :
    (∀ s : Sections U, IsCompatible (Opens.comap (mapBase φ hφ).hom U) (mappedFamily φ hφ U s)) ∧
      mappedFamily φ hφ U 1 = 1 ∧
      (∀ s t : Sections U,
        mappedFamily φ hφ U (s * t) = mappedFamily φ hφ U s * mappedFamily φ hφ U t) ∧
      mappedFamily φ hφ U 0 = 0 ∧
      (∀ s t : Sections U,
        mappedFamily φ hφ U (s + t) = mappedFamily φ hφ U s + mappedFamily φ hφ U t) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s J K hJ hK hJK
    have hI := isIdealOfDefinition_sourceIdeal φ hφ hJ
    have hIJ := sourceIdeal_le_comap φ J
    have hIK : sourceIdeal φ J ≤ Ideal.comap φ K := fun _ hx => hJK (hIJ hx)
    change transition _ hJ hK hJK (mappedComponent φ hφ U s J hJ) =
      mappedComponent φ hφ U s K hK
    rw [mappedComponent_eq φ hφ U s hI hJ hIJ,
      mappedComponent_eq φ hφ U s hI hK hIK]
    exact RingHom.congr_fun
      (componentMapOfLe_target_transition φ hφ U hI hJ hK hIJ hJK) _
  · funext J
    exact map_one (componentMapOfLe φ hφ U
      (isIdealOfDefinition_sourceIdeal φ hφ J.property) J.property (sourceIdeal_le_comap φ J.val))
  · intro s t
    funext J
    exact map_mul (componentMapOfLe φ hφ U
      (isIdealOfDefinition_sourceIdeal φ hφ J.property) J.property
      (sourceIdeal_le_comap φ J.val)) _ _
  · funext J
    exact map_zero (componentMapOfLe φ hφ U
      (isIdealOfDefinition_sourceIdeal φ hφ J.property) J.property (sourceIdeal_le_comap φ J.val))
  · intro s t
    funext J
    exact map_add (componentMapOfLe φ hφ U
      (isIdealOfDefinition_sourceIdeal φ hφ J.property) J.property
      (sourceIdeal_le_comap φ J.val)) _ _

/-- The ring homomorphism on sections induced by a continuous map of admissible rings. -/
def sectionsMap (φ : A →+* B) (hφ : Continuous φ) (U : Opens (OpenPrime A)) :
    Sections U →+* Sections (Opens.comap (mapBase φ hφ).hom U) where
  toFun s := ofCompatible _ (mappedFamily φ hφ U s) ((sectionsMap_laws φ hφ U).1 s)
  map_one' := Subtype.ext (sectionsMap_laws φ hφ U).2.1
  map_mul' s t := Subtype.ext ((sectionsMap_laws φ hφ U).2.2.1 s t)
  map_zero' := Subtype.ext (sectionsMap_laws φ hφ U).2.2.2.1
  map_add' s t := Subtype.ext ((sectionsMap_laws φ hφ U).2.2.2.2 s t)

/-- Every eligible source ideal gives the same target component of the section map. -/
theorem sectionsMap_apply_of_le (φ : A →+* B) (hφ : Continuous φ)
    (U : Opens (OpenPrime A)) {I : Ideal A} {J : Ideal B}
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hJ : TopologicalRing.Ideal.IsIdealOfDefinition J) (hIJ : I ≤ Ideal.comap φ J)
    (s : Sections U) :
    (sectionsMap φ hφ U s).component J hJ =
      componentMapOfLe φ hφ U hI hJ hIJ (s.component I hI) :=
  mappedComponent_eq φ hφ U s hI hJ hIJ

private theorem exists_compact_open_neighborhood {R : Type u} [CommRing R]
    {K : Set (PrimeSpectrum R)} (hK : IsCompact K) (U : Opens (PrimeSpectrum R))
    (hKU : K ⊆ U) :
    ∃ V : Opens (PrimeSpectrum R), IsCompact (V : Set (PrimeSpectrum R)) ∧ K ⊆ V ∧ V ≤ U := by
  classical
  let S := {f : R // PrimeSpectrum.basicOpen f ≤ U}
  have hcover : K ⊆ ⋃ f : S, (PrimeSpectrum.basicOpen f.val : Set (PrimeSpectrum R)) := by
    intro p hp
    have hpU := hKU hp
    rw [PrimeSpectrum.eq_biUnion_of_isOpen U.isOpen] at hpU
    obtain ⟨f, hf⟩ := Set.mem_iUnion.mp hpU
    obtain ⟨hfU, hpf⟩ := Set.mem_iUnion.mp hf
    exact Set.mem_iUnion.mpr ⟨⟨f, hfU⟩, hpf⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun f : S => (PrimeSpectrum.basicOpen f.val : Set (PrimeSpectrum R)))
    (fun _ => PrimeSpectrum.isOpen_basicOpen) hcover
  refine ⟨⨆ f ∈ t, PrimeSpectrum.basicOpen f.val, ?_, ?_, ?_⟩
  · simpa only [Opens.coe_iSup] using
      t.isCompact_biUnion (fun f _ => PrimeSpectrum.isCompact_basicOpen f.val)
  · simpa only [Opens.coe_iSup] using ht
  · exact iSup_le fun f => iSup_le fun _ => f.property

private theorem continuous_componentMapOfLe (φ : A →+* B) (hφ : Continuous φ)
    (U : Opens (OpenPrime A)) {I : Ideal A} {J : Ideal B}
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hJ : TopologicalRing.Ideal.IsIdealOfDefinition J) (hIJ : I ≤ Ideal.comap φ J) :
    Continuous (componentMapOfLe φ hφ U hI hJ hIJ) := by
  change Continuous[_, pseudoDiscreteComponentTopology _ J hJ] _
  refine continuous_iInf_rng.mpr fun W =>
    continuous_iInf_rng.mpr fun hW => continuous_iInf_rng.mpr fun hWV => ?_
  apply continuous_induced_rng.mpr
  let q := Ideal.quotientMap J φ hIJ
  have himage : PrimeSpectrum.comap q '' (W : Set (PrimeSpectrum (B ⧸ J))) ⊆
      pullbackOpens U I hI := by
    rintro _ ⟨p, hp, rfl⟩
    exact pullbackOpens_subset_comap_quotient φ hφ U hI hJ hIJ (hWV hp)
  obtain ⟨V, hV, hWV', hVU⟩ := exists_compact_open_neighborhood
    (hW.image (PrimeSpectrum.continuous_comap q)) (pullbackOpens U I hI) himage
  letI : TopologicalSpace ((Spec.structureSheaf (A ⧸ I)).1.obj (op V) : Type u) := ⊥
  letI : TopologicalSpace ((Spec.structureSheaf (B ⧸ J)).1.obj (op W) : Type u) := ⊥
  have hres : Continuous[pseudoDiscreteComponentTopology U I hI, ⊥]
      (((Spec.structureSheaf (A ⧸ I)).1.map (homOfLE hVU).op).hom :
        componentType U I hI → _) :=
    continuous_iff_le_induced.mpr
      (iInf_le_of_le V (iInf_le_of_le hV (iInf_le _ hVU)))
  have hpost : Continuous[⊥, ⊥]
      (StructureSheaf.comap q V W (fun p hp => hWV' ⟨p, hp, rfl⟩)) :=
    @continuous_of_discreteTopology _ ⊥ (discreteTopology_bot _) _ ⊥ _
  exact hpost.comp hres

/-- The induced section homomorphism is continuous in the inverse-limit topologies. -/
theorem continuous_sectionsMap (φ : A →+* B) (hφ : Continuous φ) (U : Opens (OpenPrime A)) :
    Continuous (sectionsMap φ hφ U) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro J
  let I : {I : Ideal A // TopologicalRing.Ideal.IsIdealOfDefinition I} :=
    ⟨sourceIdeal φ J.val, isIdealOfDefinition_sourceIdeal φ hφ J.property⟩
  have he : Continuous (fun s : ComponentFamily U => s I) := continuous_apply I
  have hv : Continuous (fun s : Sections U => s.val) := continuous_subtype_val
  exact (continuous_componentMapOfLe φ hφ U I.property J.property
    (sourceIdeal_le_comap φ J.val)).comp (he.comp hv)

/-- The continuous component of the induced morphism of structure presheaves. -/
def mapApp (φ : A →+* B) (hφ : Continuous φ) (U : (Opens (OpenPrime A))ᵒᵖ) :
    (structurePresheaf A).obj U ⟶
      ((Presheaf.pushforward TopCommRingCat (mapBase φ hφ)).obj (structurePresheaf B)).obj U :=
  ⟨sectionsMap φ hφ (unop U), continuous_sectionsMap φ hφ (unop U)⟩

/-- The induced continuous section maps commute with all restrictions. -/
theorem map_naturality (φ : A →+* B) (hφ : Continuous φ)
    {U V : (Opens (OpenPrime A))ᵒᵖ} (i : U ⟶ V) :
    (structurePresheaf A).map i ≫ mapApp φ hφ V =
      mapApp φ hφ U ≫
        ((Presheaf.pushforward TopCommRingCat (mapBase φ hφ)).obj (structurePresheaf B)).map i := by
  apply Subtype.ext
  apply RingHom.ext
  intro s
  apply Subtype.ext
  funext J
  apply Subtype.ext
  funext p
  rfl

/-- The sheaf morphism induced by a continuous homomorphism of admissible rings. -/
def mapSheafedHom (φ : A →+* B) (hφ : Continuous φ) :
    (spf B).toSheafedSpace ⟶ (spf A).toSheafedSpace :=
  SheafedSpace.fullyFaithfulForgetToPresheafedSpace.preimage
    { base := mapBase φ hφ
      c := { app := mapApp φ hφ
             naturality := fun _ _ i ↦ map_naturality φ hφ i } }

/-- The induced sheaf morphism is local on all underlying ring stalks. -/
theorem map_isLocalHom (φ : A →+* B) (hφ : Continuous φ) :
    ∀ x : (spf B).carrier,
      IsLocalHom (LocallyTopologicallyRingedSpaceCat.stalkRingHom (mapSheafedHom φ hφ) x) := sorry

/-- The contravariant local morphism of formal spectra induced by a continuous ring map. -/
def map (φ : A →+* B) (hφ : Continuous φ) :
    LocallyTopologicallyRingedSpaceCat.Hom (spf B) (spf A) :=
  LocallyTopologicallyRingedSpaceCat.Hom.ofSheafedHom
    (mapSheafedHom φ hφ) (map_isLocalHom φ hφ)

set_option backward.isDefEq.respectTransparency false in
private theorem componentMapOfLe_comp {C : Type u} [CommRing C] [TopologicalSpace C]
    [TopologicalRing.IsAdmissibleRing C] (φ : A →+* B) (hφ : Continuous φ)
    (ψ : B →+* C) (hψ : Continuous ψ) (U : Opens (OpenPrime A))
    {I : Ideal A} {J : Ideal B} {K : Ideal C}
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hJ : TopologicalRing.Ideal.IsIdealOfDefinition J)
    (hK : TopologicalRing.Ideal.IsIdealOfDefinition K)
    (hIJ : I ≤ Ideal.comap φ J) (hJK : J ≤ Ideal.comap ψ K) :
    (componentMapOfLe ψ hψ (Opens.comap (mapBase φ hφ).hom U) hJ hK hJK).comp
        (componentMapOfLe φ hφ U hI hJ hIJ) =
      componentMapOfLe (ψ.comp φ) (hψ.comp hφ) U hI hK (fun _ hx => hJK (hIJ hx)) := by
  have hq : (Ideal.quotientMap K ψ hJK).comp (Ideal.quotientMap J φ hIJ) =
      Ideal.quotientMap K (ψ.comp φ) (fun _ hx => hJK (hIJ hx)) := by
    apply Ideal.Quotient.ringHom_ext
    exact RingHom.ext fun _ => rfl
  have hc := StructureSheaf.comap_comp (Ideal.quotientMap J φ hIJ) (Ideal.quotientMap K ψ hJK)
    (pullbackOpens U I hI)
    (pullbackOpens (Opens.comap (mapBase φ hφ).hom U) J hJ)
    (pullbackOpens (Opens.comap (mapBase ψ hψ).hom (Opens.comap (mapBase φ hφ).hom U)) K hK)
    (pullbackOpens_subset_comap_quotient φ hφ U hI hJ hIJ)
    (pullbackOpens_subset_comap_quotient ψ hψ (Opens.comap (mapBase φ hφ).hom U) hJ hK hJK)
  apply RingHom.ext
  intro s
  apply Subtype.ext
  funext p
  have hright := StructureSheaf.comap_apply
    (Ideal.quotientMap K (ψ.comp φ) (fun _ hx => hJK (hIJ hx)))
    (pullbackOpens U I hI)
    (pullbackOpens (Opens.comap (mapBase (ψ.comp φ) (hψ.comp hφ)).hom U) K hK)
    (pullbackOpens_subset_comap_quotient (ψ.comp φ) (hψ.comp hφ) U hI hK
      (fun _ hx => hJK (hIJ hx))) s ⟨p.val, p.property⟩
  refine Eq.trans ?_ hright.symm
  simpa only [componentMapOfLe, instCommRingComponentType, componentType, hq,
    RingHom.coe_comp, Function.comp_apply, StructureSheaf.comap_apply]
    using (congrArg (fun t => t.val p) (RingHom.congr_fun hc s)).symm

/-- Composition of continuous ring homomorphisms induces reversed composition of local maps. -/
theorem map_comp {C : Type u} [CommRing C] [TopologicalSpace C]
    [TopologicalRing.IsAdmissibleRing C] (φ : A →+* B) (hφ : Continuous φ)
    (ψ : B →+* C) (hψ : Continuous ψ) :
    LocallyTopologicallyRingedSpaceCat.comp (map ψ hψ) (map φ hφ) =
      map (ψ.comp φ) (hψ.comp hφ) := by
  apply Subtype.ext
  change mapSheafedHom ψ hψ ≫ mapSheafedHom φ hφ = mapSheafedHom (ψ.comp φ) (hψ.comp hφ)
  refine SheafedSpace.ext _ _ ?_ ?_
  · rfl
  · apply NatTrans.ext
    funext U
    apply Subtype.ext
    apply RingHom.ext
    intro s
    apply Subtype.ext
    funext K
    let J := sourceIdeal ψ K.val
    have hJ := isIdealOfDefinition_sourceIdeal ψ hψ K.property
    have hJK := sourceIdeal_le_comap ψ K.val
    let I := sourceIdeal φ J
    have hI := isIdealOfDefinition_sourceIdeal φ hφ hJ
    have hIJ := sourceIdeal_le_comap φ J
    have hIK : I ≤ Ideal.comap (ψ.comp φ) K.val := fun _ hx => hJK (hIJ hx)
    change (sectionsMap ψ hψ (Opens.comap (mapBase φ hφ).hom (unop U))
        (sectionsMap φ hφ (unop U) s)).component K.val K.property =
      (sectionsMap (ψ.comp φ) (hψ.comp hφ) (unop U) s).component K.val K.property
    rw [sectionsMap_apply_of_le ψ hψ _ hJ K.property hJK,
      sectionsMap_apply_of_le φ hφ _ hI hJ hIJ,
      sectionsMap_apply_of_le (ψ.comp φ) (hψ.comp hφ) _ hI K.property hIK]
    exact RingHom.congr_fun (componentMapOfLe_comp φ hφ ψ hψ (unop U) hI hJ K.property hIJ hJK) _

/-- The ring homomorphism extracted from a local morphism using global sections. -/
def homToRingHom (f : LocallyTopologicallyRingedSpaceCat.Hom (spf B) (spf A)) : A →+* B :=
  (globalSectionsInvHom B).comp
    ((f.toSheafedHom.hom.c.app (op ⊤)).1.comp (globalSectionsHom A))

/-- Extraction through global sections yields a continuous ring homomorphism. -/
theorem homToContinuous_continuous
    (f : LocallyTopologicallyRingedSpaceCat.Hom (spf B) (spf A)) :
    Continuous (homToRingHom f) :=
  globalSectionsInvHom_continuous.comp
    ((f.toSheafedHom.hom.c.app (op ⊤)).2.comp globalSectionsHom_continuous)

/-- The continuous ring homomorphism corresponding to a local morphism of formal spectra. -/
def homToContinuous (f : LocallyTopologicallyRingedSpaceCat.Hom (spf B) (spf A)) :
    TopCommRingCat.of A ⟶ TopCommRingCat.of B :=
  ⟨homToRingHom f, homToContinuous_continuous f⟩

/-- Reconstructing from the extracted ring homomorphism recovers the local morphism. -/
theorem homEquiv_left_inv (f : LocallyTopologicallyRingedSpaceCat.Hom (spf B) (spf A)) :
    map (homToContinuous f).1 (homToContinuous f).2 = f := sorry

/-- Extracting from the induced local morphism recovers the continuous ring homomorphism. -/
theorem homEquiv_right_inv (φ : TopCommRingCat.of A ⟶ TopCommRingCat.of B) :
    homToContinuous (map φ.1 φ.2) = φ := by
  have hsec (a : A) : sectionsMap φ.1 φ.2 ⊤ (globalSectionsHom A a) =
      globalSectionsHom B (φ.1 a) := by
    apply Subtype.ext
    funext J
    change StructureSheaf.comap (Ideal.quotientMap J.val φ.1 (sourceIdeal_le_comap φ.1 J.val))
        (⊤ : Opens (PrimeSpectrum (A ⧸ sourceIdeal φ.1 J.val)))
        (⊤ : Opens (PrimeSpectrum (B ⧸ J.val))) _
        (algebraMap (A ⧸ sourceIdeal φ.1 J.val)
          ((Spec.structureSheaf (A ⧸ sourceIdeal φ.1 J.val)).1.obj (op ⊤))
          (Ideal.Quotient.mk (sourceIdeal φ.1 J.val) a)) =
      algebraMap (B ⧸ J.val) ((Spec.structureSheaf (B ⧸ J.val)).1.obj (op ⊤))
        ((Ideal.quotientMap J.val φ.1 (sourceIdeal_le_comap φ.1 J.val))
          (Ideal.Quotient.mk (sourceIdeal φ.1 J.val) a))
    exact StructureSheaf.toOpen_comp_comap_apply
      (Ideal.quotientMap J.val φ.1 (sourceIdeal_le_comap φ.1 J.val)) ⊤ _
  apply Subtype.ext
  apply RingHom.ext
  intro a
  change globalSectionsInvHom B (sectionsMap φ.1 φ.2 ⊤ (globalSectionsHom A a)) = φ.1 a
  rw [hsec]
  apply Eq.symm
  apply globalSectionsInvHom_unique
  intro J hJ
  exact (quotientToComponent_componentToQuotient J hJ (Ideal.Quotient.mk J (φ.1 a))).symm

/-- Local morphisms of formal spectra correspond contravariantly to continuous ring maps. -/
def homEquiv (A B : Type u) [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsAdmissibleRing A] [CommRing B] [TopologicalSpace B]
    [TopologicalRing.IsAdmissibleRing B] :
    LocallyTopologicallyRingedSpaceCat.Hom (spf B) (spf A) ≃
      (TopCommRingCat.of A ⟶ TopCommRingCat.of B) where
  toFun := homToContinuous
  invFun φ := map φ.1 φ.2
  left_inv := homEquiv_left_inv
  right_inv := homEquiv_right_inv

/-- The correspondence evaluates a local morphism by the global-sections comparison. -/
theorem homEquiv_apply (f : LocallyTopologicallyRingedSpaceCat.Hom (spf B) (spf A)) :
    homEquiv A B f = homToContinuous f := rfl

end AlgebraicGeometry.FormalSpectrum
