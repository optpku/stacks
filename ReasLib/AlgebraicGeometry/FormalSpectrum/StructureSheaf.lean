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
    DiscreteTopology (componentType U I hI) := sorry

/-- The pseudo-discrete component section rings are topological rings. -/
instance instIsTopologicalRingComponentType (U : Opens (OpenPrime A)) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    IsTopologicalRing (componentType U I hI) := sorry

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
      PrimeSpectrum.comap (Ideal.Quotient.factor hIJ) ⁻¹' pullbackOpens U I hI := sorry

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
      (∀ s : ComponentFamily U, IsCompatible U s → IsCompatible U (-s)) := sorry

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
      (ofCompatible U s h).component I hI = s ⟨I, hI⟩) ∧ IsCompatible U s := sorry

/-- The inverse-limit section rings are topological rings. -/
instance instIsTopologicalRingSections (U : Opens (OpenPrime A)) :
    IsTopologicalRing (Sections U) := sorry

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
        restrictedFamily hVU (s + t) = restrictedFamily hVU s + restrictedFamily hVU t) := sorry

/-- The ring homomorphism restricting inverse-limit sections. -/
def restriction {U V : Opens (OpenPrime A)} (hVU : V ≤ U) : Sections U →+* Sections V where
  toFun s := ofCompatible V (restrictedFamily hVU s) ((restriction_laws hVU).1 s)
  map_one' := Subtype.ext (restriction_laws hVU).2.1
  map_mul' s t := Subtype.ext ((restriction_laws hVU).2.2.1 s t)
  map_zero' := Subtype.ext (restriction_laws hVU).2.2.2.1
  map_add' s t := Subtype.ext ((restriction_laws hVU).2.2.2.2 s t)

/-- Restriction is continuous for the inverse-limit topology. -/
theorem continuous_restriction {U V : Opens (OpenPrime A)} (hVU : V ≤ U) :
    Continuous (restriction hVU : Sections U → Sections V) := sorry

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
          restrictionHom (leOfHom (unop f)) ≫ restrictionHom (leOfHom (unop g))) := sorry

/-- The presheaf of topological rings given by compatible quotient-spectrum sections. -/
def structurePresheaf (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    (TopCat.of (OpenPrime A)).Presheaf TopCommRingCat.{u} where
  obj U := TopCommRingCat.of (Sections (unop U))
  map f := restrictionHom (leOfHom (unop f))
  map_id := structurePresheaf_laws.1
  map_comp := structurePresheaf_laws.2

/-- The objects of the structure presheaf are inverse-limit section rings. -/
theorem structurePresheaf_obj (U : (Opens (OpenPrime A))ᵒᵖ) :
    (structurePresheaf A).obj U = TopCommRingCat.of (Sections (unop U)) := sorry

/-- The maps of the structure presheaf are the continuous restriction homomorphisms. -/
theorem structurePresheaf_map {U V : (Opens (OpenPrime A))ᵒᵖ} (f : U ⟶ V) :
    (structurePresheaf A).map f = restrictionHom (leOfHom (unop f)) := sorry

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
