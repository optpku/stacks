/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Topology.Algebra.Ring.Basic
public import ReasLib.AlgebraicGeometry.LocallyTopologicallyRingedSpace
public import ReasLib.AlgebraicGeometry.FormalSpectrum.OpenPrime
public import ReasLib.RingTheory.Topology.Adic.Complete

@[expose] public section

universe u

noncomputable section

open CategoryTheory Opposite TopCat Topology TopologicalSpace
open AlgebraicGeometry.Spec (structureSheaf)

namespace AlgebraicGeometry.FormalSpectrum

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- The open of a quotient spectrum corresponding to an open of the formal spectrum. -/
def pullbackOpens (U : Opens (OpenPrime A)) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) : Opens (PrimeSpectrum (A ⧸ I)) :=
  Opens.comap (OpenPrime.homeomorphQuotientInv I hI) U

/-- Sections of the quotient-spectrum structure sheaf on the corresponding open. -/
def componentType (U : Opens (OpenPrime A)) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) : Type u :=
  ((structureSheaf (A ⧸ I)).1.obj (op (pullbackOpens U I hI)) : Type u)

/-- Component sections inherit their commutative ring structure from the structure sheaf. -/
instance instCommRingComponentType (U : Opens (OpenPrime A)) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) : CommRing (componentType U I hI) :=
  inferInstanceAs
    (CommRing ((structureSheaf (A ⧸ I)).1.obj (op (pullbackOpens U I hI)) : Type u))

/-- The initial topology given by restrictions to discrete sections over compact opens. -/
@[reducible] def pseudoDiscreteComponentTopology (U : Opens (OpenPrime A)) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    TopologicalSpace (componentType U I hI) :=
  ⨅ (V : Opens (PrimeSpectrum (A ⧸ I))),
    ⨅ (_ : IsCompact (V : Set (PrimeSpectrum (A ⧸ I)))),
      ⨅ (hVU : V ≤ pullbackOpens U I hI),
        TopologicalSpace.induced
          ((structureSheaf (A ⧸ I)).1.map (homOfLE hVU).op).hom
          (⊥ : TopologicalSpace ((structureSheaf (A ⧸ I)).1.obj (op V) : Type u))

/-- Component sections carry the pseudo-discrete topology. -/
instance instTopologicalSpaceComponentType (U : Opens (OpenPrime A)) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    TopologicalSpace (componentType U I hI) := pseudoDiscreteComponentTopology U I hI

/-- Component sections over compact opens have the discrete topology. -/
theorem isDiscrete_componentType_of_isCompact (U : Opens (OpenPrime A)) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hU : IsCompact (pullbackOpens U I hI : Set (PrimeSpectrum (A ⧸ I)))) :
    DiscreteTopology (componentType U I hI) := by
  refine ⟨le_antisymm ?_ bot_le⟩
  change pseudoDiscreteComponentTopology U I hI ≤ ⊥
  have h :=
    (iInf_le_of_le (pullbackOpens U I hI)
      (iInf_le_of_le hU (iInf_le _ le_rfl)) :
      pseudoDiscreteComponentTopology U I hI ≤
        TopologicalSpace.induced
          ((structureSheaf (A ⧸ I)).1.map (homOfLE le_rfl).op).hom ⊥)
  have hid : TopologicalSpace.induced
      ((structureSheaf (A ⧸ I)).1.map (homOfLE le_rfl).op).hom ⊥ =
        (⊥ : TopologicalSpace (componentType U I hI)) := by
    simp [induced_id]
    rfl
  exact h.trans_eq hid

/-- The pseudo-discrete component section rings are topological rings. -/
instance instIsTopologicalRingComponentType (U : Opens (OpenPrime A)) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    IsTopologicalRing (componentType U I hI) := by
  refine
    { toContinuousAdd := continuousAdd_iInf fun V =>
        continuousAdd_iInf fun _ => continuousAdd_iInf fun hVU => ?_
      toContinuousMul := continuousMul_iInf fun V =>
        continuousMul_iInf fun _ => continuousMul_iInf fun hVU => ?_
      toContinuousNeg := continuousNeg_iInf fun V =>
        continuousNeg_iInf fun _ => continuousNeg_iInf fun hVU => ?_ }
  · refine @continuousAdd_induced _ _ _ _ _ _ _ ⊥ ?_
      ((structureSheaf (A ⧸ I)).1.map (homOfLE hVU).op).hom
    exact @continuousAdd_of_discreteTopology _ ⊥ _ (discreteTopology_bot _)
  · refine @continuousMul_induced _ _ _ _ _ _ _ ⊥ ?_
      ((structureSheaf (A ⧸ I)).1.map (homOfLE hVU).op).hom
    exact @continuousMul_of_discreteTopology _ ⊥ _ (discreteTopology_bot _)
  · refine @ContinuousNeg.induced _ _ _ _ _ _ _ ⊥ ?_
      ((structureSheaf (A ⧸ I)).1.map (homOfLE hVU).op).hom
    exact @continuousNeg_of_discreteTopology _ ⊥ _ (discreteTopology_bot _)

/-- Restriction of quotient-spectrum sections along an inclusion of opens. -/
def componentRestrict {U V : Opens (OpenPrime A)} (hVU : V ≤ U) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    componentType U I hI →+* componentType V I hI :=
  ((structureSheaf (A ⧸ I)).1.map
    (homOfLE (Opens.comap_mono (OpenPrime.homeomorphQuotientInv I hI) hVU)).op).hom

/-- Quotient factor maps pull the corresponding opens back to opens containing the target. -/
theorem pullbackOpens_subset_comap_factor (U : Opens (OpenPrime A)) {I J : Ideal A}
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hJ : TopologicalRing.Ideal.IsIdealOfDefinition J) (hIJ : I ≤ J) :
    (pullbackOpens U J hJ : Set (PrimeSpectrum (A ⧸ J))) ⊆
      PrimeSpectrum.comap (Ideal.Quotient.factor hIJ) ⁻¹' pullbackOpens U I hI := by
  intro q hq
  change OpenPrime.homeomorphQuotientInv I hI
    (PrimeSpectrum.comap (Ideal.Quotient.factor hIJ) q) ∈ U
  change OpenPrime.homeomorphQuotientInv J hJ q ∈ U at hq
  have h : OpenPrime.homeomorphQuotientInv I hI
      (PrimeSpectrum.comap (Ideal.Quotient.factor hIJ) q) =
        OpenPrime.homeomorphQuotientInv J hJ q := by
    apply Subtype.ext
    change PrimeSpectrum.comap (Ideal.Quotient.mk I)
      (PrimeSpectrum.comap (Ideal.Quotient.factor hIJ) q) =
        PrimeSpectrum.comap (Ideal.Quotient.mk J) q
    rw [← PrimeSpectrum.comap_comp_apply, Ideal.Quotient.factor_comp_mk]
  rwa [h]

/-- Transition of component sections induced by a quotient factor homomorphism. -/
def transition (U : Opens (OpenPrime A)) {I J : Ideal A}
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hJ : TopologicalRing.Ideal.IsIdealOfDefinition J) (hIJ : I ≤ J) :
    componentType U I hI →+* componentType U J hJ :=
  StructureSheaf.comap (Ideal.Quotient.factor hIJ)
    (pullbackOpens U I hI) (pullbackOpens U J hJ)
    (pullbackOpens_subset_comap_factor U hI hJ hIJ)

/-- Families of quotient-spectrum sections indexed by all ideals of definition. -/
abbrev ComponentFamily (U : Opens (OpenPrime A)) :=
  ∀ I : {I : Ideal A // TopologicalRing.Ideal.IsIdealOfDefinition I},
    componentType U I.val I.property

/-- Compatibility of a family under all quotient transition homomorphisms. -/
def IsCompatible (U : Opens (OpenPrime A)) (s : ComponentFamily U) : Prop :=
  ∀ {I J : Ideal A} (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hJ : TopologicalRing.Ideal.IsIdealOfDefinition J) (hIJ : I ≤ J),
    transition U hI hJ hIJ (s ⟨I, hI⟩) = s ⟨J, hJ⟩

/-- Compatible families contain zero and one and are closed under ring operations. -/
theorem sectionSubring_laws (U : Opens (OpenPrime A)) :
    IsCompatible U 0 ∧ IsCompatible U 1 ∧
      (∀ s t : ComponentFamily U, IsCompatible U s → IsCompatible U t →
        IsCompatible U (s + t)) ∧
      (∀ s t : ComponentFamily U, IsCompatible U s → IsCompatible U t →
        IsCompatible U (s * t)) ∧
      (∀ s : ComponentFamily U, IsCompatible U s → IsCompatible U (-s)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro I J hI hJ hIJ
    exact map_zero _
  · intro I J hI hJ hIJ
    exact map_one _
  · intro s t hs ht I J hI hJ hIJ
    exact (map_add (transition U hI hJ hIJ) (s ⟨I, hI⟩) (t ⟨I, hI⟩)).trans
      (congrArg₂ (· + ·) (hs hI hJ hIJ) (ht hI hJ hIJ))
  · intro s t hs ht I J hI hJ hIJ
    exact (map_mul (transition U hI hJ hIJ) (s ⟨I, hI⟩) (t ⟨I, hI⟩)).trans
      (congrArg₂ (· * ·) (hs hI hJ hIJ) (ht hI hJ hIJ))
  · intro s hs I J hI hJ hIJ
    exact (map_neg (transition U hI hJ hIJ) (s ⟨I, hI⟩)).trans
      (congrArg Neg.neg (hs hI hJ hIJ))

/-- The subring of compatible families of quotient-spectrum sections. -/
def sectionSubring (U : Opens (OpenPrime A)) : Subring (ComponentFamily U) where
  carrier := {s | IsCompatible U s}
  zero_mem' := (sectionSubring_laws U).1
  one_mem' := (sectionSubring_laws U).2.1
  add_mem' := (sectionSubring_laws U).2.2.1 _ _
  mul_mem' := (sectionSubring_laws U).2.2.2.1 _ _
  neg_mem' := (sectionSubring_laws U).2.2.2.2 _

/-- Formal-spectrum sections, with the inherited subring algebra and product-subspace topology. -/
abbrev Sections (U : Opens (OpenPrime A)) : Type u := sectionSubring U

/-- The component of a section at an ideal of definition. -/
def Sections.component {U : Opens (OpenPrime A)} (s : Sections U) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) : componentType U I hI := s.val ⟨I, hI⟩

/-- Construct a section from a compatible family. -/
def ofCompatible (U : Opens (OpenPrime A)) (s : ComponentFamily U)
    (h : IsCompatible U s) : Sections U := ⟨s, h⟩

/-- The section constructor retains every component and the compatibility condition. -/
theorem ofCompatible_spec (U : Opens (OpenPrime A)) (s : ComponentFamily U)
    (h : IsCompatible U s) :
    (∀ (I : Ideal A) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I),
      (ofCompatible U s h).component I hI = s ⟨I, hI⟩) ∧ IsCompatible U s :=
  ⟨fun _ _ => rfl, h⟩

/-- The inverse-limit section rings are topological rings. -/
instance instIsTopologicalRingSections (U : Opens (OpenPrime A)) :
    IsTopologicalRing (Sections U) := inferInstance

/-- Componentwise restriction of a section family. -/
def restrictedFamily {U V : Opens (OpenPrime A)} (hVU : V ≤ U) (s : Sections U) :
    ComponentFamily V :=
  fun I ↦ componentRestrict hVU I.val I.property (s.component I.val I.property)

/-- Componentwise restriction preserves compatibility and the ring operations. -/
theorem restriction_laws {U V : Opens (OpenPrime A)} (hVU : V ≤ U) :
    (∀ s : Sections U, IsCompatible V (restrictedFamily hVU s)) ∧
      restrictedFamily hVU 1 = 1 ∧
      (∀ s t : Sections U,
        restrictedFamily hVU (s * t) = restrictedFamily hVU s * restrictedFamily hVU t) ∧
      restrictedFamily hVU 0 = 0 ∧
      (∀ s t : Sections U,
        restrictedFamily hVU (s + t) = restrictedFamily hVU s + restrictedFamily hVU t) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s I J hI hJ hIJ
    have hcomm (t : componentType U I hI) :
        transition V hI hJ hIJ (componentRestrict hVU I hI t) =
          componentRestrict hVU J hJ (transition U hI hJ hIJ t) := by
      apply Subtype.ext
      funext p
      rfl
    change transition V hI hJ hIJ (componentRestrict hVU I hI (s.component I hI)) =
      componentRestrict hVU J hJ (s.component J hJ)
    rw [hcomm]
    exact congrArg (componentRestrict hVU J hJ) (s.property hI hJ hIJ)
  · funext I
    exact map_one (componentRestrict hVU I.val I.property)
  · intro s t
    funext I
    exact map_mul (componentRestrict hVU I.val I.property) _ _
  · funext I
    exact map_zero (componentRestrict hVU I.val I.property)
  · intro s t
    funext I
    exact map_add (componentRestrict hVU I.val I.property) _ _

/-- The ring homomorphism restricting inverse-limit sections. -/
def restriction {U V : Opens (OpenPrime A)} (hVU : V ≤ U) : Sections U →+* Sections V where
  toFun s := ofCompatible V (restrictedFamily hVU s) ((restriction_laws hVU).1 s)
  map_one' := Subtype.ext (restriction_laws hVU).2.1
  map_mul' s t := Subtype.ext ((restriction_laws hVU).2.2.1 s t)
  map_zero' := Subtype.ext (restriction_laws hVU).2.2.2.1
  map_add' s t := Subtype.ext ((restriction_laws hVU).2.2.2.2 s t)

/-- Restriction is continuous for the inverse-limit topology. -/
theorem continuous_restriction {U V : Opens (OpenPrime A)} (hVU : V ≤ U) :
    Continuous (restriction hVU : Sections U → Sections V) := by
  have hc (I : Ideal A) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
      Continuous (componentRestrict hVU I hI) := by
    change Continuous[_, pseudoDiscreteComponentTopology V I hI] _
    refine continuous_iInf_rng.mpr fun W =>
      continuous_iInf_rng.mpr fun hW => continuous_iInf_rng.mpr fun hWV => ?_
    apply continuous_induced_rng.mpr
    have hWU : W ≤ pullbackOpens U I hI :=
      hWV.trans (Opens.comap_mono (OpenPrime.homeomorphQuotientInv I hI) hVU)
    have hcont : Continuous[pseudoDiscreteComponentTopology U I hI, ⊥]
        (((structureSheaf (A ⧸ I)).1.map (homOfLE hWU).op).hom :
          componentType U I hI → _) :=
      continuous_iff_le_induced.mpr
        (iInf_le_of_le W (iInf_le_of_le hW (iInf_le _ hWU)))
    exact hcont
  apply Continuous.subtype_mk
  apply continuous_pi
  intro I
  exact (hc I.val I.property).comp ((continuous_apply I).comp continuous_subtype_val)

/-- Continuous restriction of sections, bundled as a morphism of topological rings. -/
def restrictionHom {U V : Opens (OpenPrime A)} (hVU : V ≤ U) :
    TopCommRingCat.of (Sections U) ⟶ TopCommRingCat.of (Sections V) :=
  ⟨restriction hVU, continuous_restriction hVU⟩

/-- The continuous restrictions satisfy identity and composition laws. -/
theorem structurePresheaf_laws :
    (∀ U : (Opens (OpenPrime A))ᵒᵖ,
      restrictionHom (leOfHom (unop (𝟙 U))) = 𝟙 (TopCommRingCat.of (Sections (unop U)))) ∧
      (∀ {U V W : (Opens (OpenPrime A))ᵒᵖ} (f : U ⟶ V) (g : V ⟶ W),
        restrictionHom (leOfHom (unop (f ≫ g))) =
          restrictionHom (leOfHom (unop f)) ≫ restrictionHom (leOfHom (unop g))) := by
  constructor
  · intro U
    apply Subtype.ext
    apply RingHom.ext
    intro s
    apply Subtype.ext
    funext I
    apply Subtype.ext
    funext p
    rfl
  · intro U V W f g
    apply Subtype.ext
    apply RingHom.ext
    intro s
    apply Subtype.ext
    funext I
    apply Subtype.ext
    funext p
    rfl

/-- The presheaf of topological rings given by compatible quotient-spectrum sections. -/
def structurePresheaf (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    (TopCat.of (OpenPrime A)).Presheaf TopCommRingCat.{u} where
  obj U := TopCommRingCat.of (Sections (unop U))
  map f := restrictionHom (leOfHom (unop f))
  map_id := structurePresheaf_laws.1
  map_comp := structurePresheaf_laws.2

/-- The objects of the structure presheaf are inverse-limit section rings. -/
theorem structurePresheaf_obj (U : (Opens (OpenPrime A))ᵒᵖ) :
    (structurePresheaf A).obj U = TopCommRingCat.of (Sections (unop U)) := rfl

/-- The maps of the structure presheaf are the continuous restriction homomorphisms. -/
theorem structurePresheaf_map {U V : (Opens (OpenPrime A))ᵒᵖ} (f : U ⟶ V) :
    (structurePresheaf A).map f = restrictionHom (leOfHom (unop f)) := rfl

/-- The inverse-limit structure presheaf satisfies the sheaf condition. -/
theorem structurePresheaf_isSheaf : (structurePresheaf A).IsSheaf := sorry

/-- The sheafed space of open primes equipped with the inverse-limit structure sheaf. -/
def sheafedSpace (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    SheafedSpace TopCommRingCat.{u} where
  carrier := TopCat.of (OpenPrime A)
  presheaf := structurePresheaf A
  IsSheaf := structurePresheaf_isSheaf

/-- The underlying ring stalks of an admissible ring's formal spectrum are local rings. -/
theorem stalk_isLocalRing {A : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsAdmissibleRing A] (x : OpenPrime A) :
    IsLocalRing ((LocallyTopologicallyRingedSpaceCat.ringPresheaf (sheafedSpace A)).stalk x) := sorry

/-- The formal spectrum of an admissible ring as a locally topologically ringed space. -/
def spf (A : Type u) [CommRing A] [TopologicalSpace A] [TopologicalRing.IsAdmissibleRing A] :
    LocallyTopologicallyRingedSpaceCat.{u} :=
  LocallyTopologicallyRingedSpaceCat.ofSheafedSpace (sheafedSpace A) stalk_isLocalRing

end AlgebraicGeometry.FormalSpectrum
