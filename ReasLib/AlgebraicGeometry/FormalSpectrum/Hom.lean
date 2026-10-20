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
      PrimeSpectrum.comap (Ideal.quotientMap J φ hIJ) ⁻¹' pullbackOpens U I hI := sorry

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
    TopologicalRing.Ideal.IsIdealOfDefinition (sourceIdeal φ J) := sorry

/-- The source ideal is contained in the inverse image of the target ideal. -/
theorem sourceIdeal_le_comap (φ : A →+* B) (J : Ideal B) :
    sourceIdeal φ J ≤ Ideal.comap φ J :=
  inf_le_right

/-- The inverse image of an ideal of definition contains an ideal of definition. -/
theorem exists_isIdealOfDefinition_le_comap (φ : A →+* B) (hφ : Continuous φ)
    {J : Ideal B} (hJ : TopologicalRing.Ideal.IsIdealOfDefinition J) :
    ∃ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I ∧ I ≤ Ideal.comap φ J :=
  ⟨sourceIdeal φ J, isIdealOfDefinition_sourceIdeal φ hφ hJ, sourceIdeal_le_comap φ J⟩

/-- Each target component is uniquely determined by every eligible source quotient component. -/
theorem sectionsMapComponent_existsUnique (φ : A →+* B) (hφ : Continuous φ)
    (U : Opens (OpenPrime A)) (s : Sections U) (J : Ideal B)
    (hJ : TopologicalRing.Ideal.IsIdealOfDefinition J) :
    ∃! t : componentType (Opens.comap (mapBase φ hφ).hom U) J hJ,
      ∀ (I : Ideal A) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
        (hIJ : I ≤ Ideal.comap φ J), t = componentMapOfLe φ hφ U hI hJ hIJ (s.component I hI) := sorry

/-- The `J`-component of the induced section map, computed from the component of the source
section at `sourceIdeal φ J`. -/
def mappedComponent (φ : A →+* B) (hφ : Continuous φ)
    (U : Opens (OpenPrime A)) (s : Sections U) (J : Ideal B)
    (hJ : TopologicalRing.Ideal.IsIdealOfDefinition J) :
    componentType (Opens.comap (mapBase φ hφ).hom U) J hJ :=
  componentMapOfLe φ hφ U (isIdealOfDefinition_sourceIdeal φ hφ hJ) hJ
    (sourceIdeal_le_comap φ J)
    (s.component (sourceIdeal φ J) (isIdealOfDefinition_sourceIdeal φ hφ hJ))

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
        mappedFamily φ hφ U (s + t) = mappedFamily φ hφ U s + mappedFamily φ hφ U t) := sorry

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
      componentMapOfLe φ hφ U hI hJ hIJ (s.component I hI) := sorry

/-- The induced section homomorphism is continuous in the inverse-limit topologies. -/
theorem continuous_sectionsMap (φ : A →+* B) (hφ : Continuous φ) (U : Opens (OpenPrime A)) :
    Continuous (sectionsMap φ hφ U) := sorry

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
        ((Presheaf.pushforward TopCommRingCat (mapBase φ hφ)).obj (structurePresheaf B)).map i := sorry

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

/-- Composition of continuous ring homomorphisms induces reversed composition of local maps. -/
theorem map_comp {C : Type u} [CommRing C] [TopologicalSpace C]
    [TopologicalRing.IsAdmissibleRing C] (φ : A →+* B) (hφ : Continuous φ)
    (ψ : B →+* C) (hψ : Continuous ψ) :
    LocallyTopologicallyRingedSpaceCat.comp (map ψ hψ) (map φ hφ) =
      map (ψ.comp φ) (hψ.comp hφ) := sorry

/-- The ring homomorphism extracted from a local morphism using global sections. -/
def homToRingHom (f : LocallyTopologicallyRingedSpaceCat.Hom (spf B) (spf A)) : A →+* B :=
  (globalSectionsInvHom B).comp
    ((f.toSheafedHom.hom.c.app (op ⊤)).1.comp (globalSectionsHom A))

/-- Extraction through global sections yields a continuous ring homomorphism. -/
theorem homToContinuous_continuous
    (f : LocallyTopologicallyRingedSpaceCat.Hom (spf B) (spf A)) :
    Continuous (homToRingHom f) := sorry

/-- The continuous ring homomorphism corresponding to a local morphism of formal spectra. -/
def homToContinuous (f : LocallyTopologicallyRingedSpaceCat.Hom (spf B) (spf A)) :
    TopCommRingCat.of A ⟶ TopCommRingCat.of B :=
  ⟨homToRingHom f, homToContinuous_continuous f⟩

/-- Reconstructing from the extracted ring homomorphism recovers the local morphism. -/
theorem homEquiv_left_inv (f : LocallyTopologicallyRingedSpaceCat.Hom (spf B) (spf A)) :
    map (homToContinuous f).1 (homToContinuous f).2 = f := sorry

/-- Extracting from the induced local morphism recovers the continuous ring homomorphism. -/
theorem homEquiv_right_inv (φ : TopCommRingCat.of A ⟶ TopCommRingCat.of B) :
    homToContinuous (map φ.1 φ.2) = φ := sorry

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
    homEquiv A B f = homToContinuous f := sorry

end AlgebraicGeometry.FormalSpectrum
