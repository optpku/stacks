/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.TransferInstance
public import Mathlib.Topology.Algebra.Ring.Basic
public import ReasLib.AlgebraicGeometry.LocallyTopologicallyRingedSpace
public import ReasLib.AlgebraicGeometry.FormalSpectrum.OpenPrime
public import ReasLib.RingTheory.Topology.WeakIdealBasis

@[expose] public section

universe u

noncomputable section

open CategoryTheory Opposite TopCat Topology TopologicalSpace
open AlgebraicGeometry.Spec (structureSheaf)

namespace AlgebraicGeometry.McQuillan.FormalSpectrum

namespace OpenPrime

variable {A : Type u} [CommRing A] [TopologicalSpace A]

/-- The image of an open prime modulo a weak ideal of definition is prime. -/
theorem isPrime_map_quotient [IsTopologicalRing A] (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsWeakIdealOfDefinition I) (p : AlgebraicGeometry.FormalSpectrum.OpenPrime A) :
    (Ideal.map (Ideal.Quotient.mk I) p.val.asIdeal).IsPrime := sorry

/-- The quotient prime obtained by taking the image of an open prime ideal. -/
def toQuotient [IsTopologicalRing A] (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsWeakIdealOfDefinition I) (p : AlgebraicGeometry.FormalSpectrum.OpenPrime A) :
    PrimeSpectrum (A ⧸ I) :=
  ⟨Ideal.map (Ideal.Quotient.mk I) p.val.asIdeal, isPrime_map_quotient I hI p⟩

/-- Quotient image and pullback are continuous inverse maps for a weak ideal of definition. -/
theorem homeomorphQuotient_laws [IsTopologicalRing A] (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsWeakIdealOfDefinition I) :
    Function.LeftInverse (AlgebraicGeometry.FormalSpectrum.OpenPrime.ofQuotient I hI.1) (toQuotient I hI) ∧
      Function.RightInverse (AlgebraicGeometry.FormalSpectrum.OpenPrime.ofQuotient I hI.1) (toQuotient I hI) ∧
      Continuous (toQuotient I hI) ∧ Continuous (AlgebraicGeometry.FormalSpectrum.OpenPrime.ofQuotient I hI.1) := sorry

/-- Open primes are homeomorphic to the spectrum of the quotient by a weak ideal of definition. -/
def homeomorphQuotient [IsTopologicalRing A] (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsWeakIdealOfDefinition I) :
    AlgebraicGeometry.FormalSpectrum.OpenPrime A ≃ₜ PrimeSpectrum (A ⧸ I) where
  toFun := toQuotient I hI
  invFun := AlgebraicGeometry.FormalSpectrum.OpenPrime.ofQuotient I hI.1
  left_inv := (homeomorphQuotient_laws I hI).1
  right_inv := (homeomorphQuotient_laws I hI).2.1
  continuous_toFun := (homeomorphQuotient_laws I hI).2.2.1
  continuous_invFun := (homeomorphQuotient_laws I hI).2.2.2

/-- The quotient-spectrum homeomorphism evaluates to the ideal-image map. -/
theorem homeomorphQuotient_apply [IsTopologicalRing A] (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsWeakIdealOfDefinition I)
    (p : AlgebraicGeometry.FormalSpectrum.OpenPrime A) :
    homeomorphQuotient I hI p = toQuotient I hI p := rfl

/-- The continuous inverse of the quotient-spectrum homeomorphism. -/
def homeomorphQuotientInv [IsTopologicalRing A] (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsWeakIdealOfDefinition I) :
    C(PrimeSpectrum (A ⧸ I), AlgebraicGeometry.FormalSpectrum.OpenPrime A) :=
  ⟨(homeomorphQuotient I hI).symm, (homeomorphQuotient I hI).continuous_invFun⟩

/-- The continuous inverse has the same point map as the inverse homeomorphism. -/
theorem homeomorphQuotientInv_apply [IsTopologicalRing A] (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsWeakIdealOfDefinition I) (q : PrimeSpectrum (A ⧸ I)) :
    homeomorphQuotientInv I hI q = (homeomorphQuotient I hI).symm q := rfl

end OpenPrime

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
variable {T : Type u} [TopologicalSpace T]
variable (e : T ≃ₜ AlgebraicGeometry.FormalSpectrum.OpenPrime A)

/-- The open of a quotient spectrum corresponding to an open of the formal spectrum. -/
def pullbackOpens (U : Opens T) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsWeakIdealOfDefinition I) : Opens (PrimeSpectrum (A ⧸ I)) :=
  Opens.comap
    ⟨e.symm ∘ OpenPrime.homeomorphQuotientInv I hI,
      e.symm.continuous.comp (OpenPrime.homeomorphQuotientInv I hI).continuous⟩ U

/-- Sections of the quotient-spectrum structure sheaf on the corresponding open. -/
def componentType (U : Opens T) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsWeakIdealOfDefinition I) : Type u :=
  ((structureSheaf (A ⧸ I)).1.obj (op (pullbackOpens e U I hI)) : Type u)

/-- Component sections inherit their commutative ring structure from the structure sheaf. -/
instance instCommRingComponentType (U : Opens T) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsWeakIdealOfDefinition I) : CommRing (componentType e U I hI) :=
  inferInstanceAs
    (CommRing ((structureSheaf (A ⧸ I)).1.obj (op (pullbackOpens e U I hI)) : Type u))

/-- The initial topology given by restrictions to discrete sections over compact opens. -/
@[reducible] def pseudoDiscreteComponentTopology (U : Opens T) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsWeakIdealOfDefinition I) :
    TopologicalSpace (componentType e U I hI) :=
  ⨅ (V : Opens (PrimeSpectrum (A ⧸ I))),
    ⨅ (_ : IsCompact (V : Set (PrimeSpectrum (A ⧸ I)))),
      ⨅ (hVU : V ≤ pullbackOpens e U I hI),
        TopologicalSpace.induced
          ((structureSheaf (A ⧸ I)).1.map (homOfLE hVU).op).hom
          (⊥ : TopologicalSpace ((structureSheaf (A ⧸ I)).1.obj (op V) : Type u))

/-- Component sections carry the pseudo-discrete topology. -/
instance instTopologicalSpaceComponentType (U : Opens T) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsWeakIdealOfDefinition I) :
    TopologicalSpace (componentType e U I hI) := pseudoDiscreteComponentTopology e U I hI

/-- The pseudo-discrete component section rings are topological rings. -/
instance instIsTopologicalRingComponentType (U : Opens T) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsWeakIdealOfDefinition I) :
    IsTopologicalRing (componentType e U I hI) := sorry

/-- Restriction of quotient-spectrum sections along an inclusion of opens. -/
def componentRestrict {U V : Opens T} (hVU : V ≤ U) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsWeakIdealOfDefinition I) :
    componentType e U I hI →+* componentType e V I hI :=
  ((structureSheaf (A ⧸ I)).1.map
    (homOfLE (Opens.comap_mono
      ⟨e.symm ∘ OpenPrime.homeomorphQuotientInv I hI,
        e.symm.continuous.comp (OpenPrime.homeomorphQuotientInv I hI).continuous⟩ hVU)).op).hom

/-- Quotient factor maps pull the corresponding opens back to opens containing the target. -/
theorem pullbackOpens_subset_comap_factor (U : Opens T) {I J : Ideal A}
    (hI : TopologicalRing.Ideal.IsWeakIdealOfDefinition I)
    (hJ : TopologicalRing.Ideal.IsWeakIdealOfDefinition J) (hIJ : I ≤ J) :
    (pullbackOpens e U J hJ : Set (PrimeSpectrum (A ⧸ J))) ⊆
      PrimeSpectrum.comap (Ideal.Quotient.factor hIJ) ⁻¹' pullbackOpens e U I hI := sorry

/-- Transition of component sections induced by a quotient factor homomorphism. -/
def transition (U : Opens T) {I J : Ideal A}
    (hI : TopologicalRing.Ideal.IsWeakIdealOfDefinition I)
    (hJ : TopologicalRing.Ideal.IsWeakIdealOfDefinition J) (hIJ : I ≤ J) :
    componentType e U I hI →+* componentType e U J hJ :=
  StructureSheaf.comap (Ideal.Quotient.factor hIJ)
    (pullbackOpens e U I hI) (pullbackOpens e U J hJ)
    (pullbackOpens_subset_comap_factor e U hI hJ hIJ)

/-- Families of quotient-spectrum sections indexed by all weak ideals of definition. -/
abbrev ComponentFamily (U : Opens T) :=
  ∀ (I : Ideal A) (hI : TopologicalRing.Ideal.IsWeakIdealOfDefinition I),
    componentType e U I hI

/-- Curried component families inherit the pointwise ring structure on weak-ideal-indexed families. -/
instance instCommRingComponentFamily (U : Opens T) : CommRing (ComponentFamily e U) :=
  ({ toFun := fun s I ↦ s I.val I.property
     invFun := fun s I hI ↦ s ⟨I, hI⟩
     left_inv := fun _ ↦ rfl
     right_inv := fun _ ↦ rfl } :
    ComponentFamily e U ≃
      ∀ I : {I : Ideal A // TopologicalRing.Ideal.IsWeakIdealOfDefinition I},
        componentType e U I.val I.property).commRing

/-- Component families carry the product topology indexed by the weak ideals of definition. -/
instance instTopologicalSpaceComponentFamily (U : Opens T) :
    TopologicalSpace (ComponentFamily e U) :=
  TopologicalSpace.induced
    (fun (s : ComponentFamily e U)
      (I : {I : Ideal A // TopologicalRing.Ideal.IsWeakIdealOfDefinition I}) ↦
        s I.val I.property) inferInstance

/-- Compatibility of a family under all quotient transition homomorphisms. -/
def IsCompatible (U : Opens T) (s : ComponentFamily e U) : Prop :=
  ∀ {I J : Ideal A} (hI : TopologicalRing.Ideal.IsWeakIdealOfDefinition I)
    (hJ : TopologicalRing.Ideal.IsWeakIdealOfDefinition J) (hIJ : I ≤ J),
    transition e U hI hJ hIJ (s I hI) = s J hJ

/-- Compatible families contain zero and one and are closed under ring operations. -/
theorem sectionSubring_laws (U : Opens T) :
    IsCompatible e U 0 ∧ IsCompatible e U 1 ∧
      (∀ s t : ComponentFamily e U, IsCompatible e U s → IsCompatible e U t →
        IsCompatible e U (s + t)) ∧
      (∀ s t : ComponentFamily e U, IsCompatible e U s → IsCompatible e U t →
        IsCompatible e U (s * t)) ∧
      (∀ s : ComponentFamily e U, IsCompatible e U s → IsCompatible e U (-s)) := sorry

/-- The subring of compatible families of quotient-spectrum sections. -/
def sectionSubring (U : Opens T) : Subring (ComponentFamily e U) where
  carrier := {s | IsCompatible e U s}
  zero_mem' := (sectionSubring_laws e U).1
  one_mem' := (sectionSubring_laws e U).2.1
  add_mem' := (sectionSubring_laws e U).2.2.1 _ _
  mul_mem' := (sectionSubring_laws e U).2.2.2.1 _ _
  neg_mem' := (sectionSubring_laws e U).2.2.2.2 _

/-- Formal-spectrum sections, with the inherited subring algebra and product-subspace topology. -/
abbrev Sections (U : Opens T) : Type u := sectionSubring e U

variable {e} in
/-- The component of a section at a weak ideal of definition. -/
def Sections.component {U : Opens T} (s : Sections e U) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsWeakIdealOfDefinition I) : componentType e U I hI := s.val I hI

/-- Construct a section from a compatible family. -/
def Sections.ofCompatible (U : Opens T) (s : ComponentFamily e U)
    (h : IsCompatible e U s) : Sections e U := ⟨s, h⟩

/-- The section constructor retains every component and the compatibility condition. -/
theorem Sections.ofCompatible_spec (U : Opens T) (s : ComponentFamily e U)
    (h : IsCompatible e U s) :
    (∀ (I : Ideal A) (hI : TopologicalRing.Ideal.IsWeakIdealOfDefinition I),
      (Sections.ofCompatible e U s h).component I hI = s I hI) ∧ IsCompatible e U s := ⟨fun _ _ ↦ rfl, h⟩

/-- The inverse-limit section rings are topological rings. -/
instance instIsTopologicalRingSections (U : Opens T) :
    IsTopologicalRing (Sections e U) := sorry

/-- Componentwise restriction of a section family. -/
def restrictedFamily {U V : Opens T} (hVU : V ≤ U) (s : Sections e U) :
    ComponentFamily e V :=
  fun I hI ↦ componentRestrict e hVU I hI (s.component I hI)

/-- Componentwise restriction preserves compatibility and the ring operations. -/
theorem restriction_laws {U V : Opens T} (hVU : V ≤ U) :
    (∀ s : Sections e U, IsCompatible e V (restrictedFamily e hVU s)) ∧
      restrictedFamily e hVU 1 = 1 ∧
      (∀ s t : Sections e U,
        restrictedFamily e hVU (s * t) = restrictedFamily e hVU s * restrictedFamily e hVU t) ∧
      restrictedFamily e hVU 0 = 0 ∧
      (∀ s t : Sections e U,
        restrictedFamily e hVU (s + t) = restrictedFamily e hVU s + restrictedFamily e hVU t) := sorry

/-- The ring homomorphism restricting inverse-limit sections. -/
def restriction {U V : Opens T} (hVU : V ≤ U) : Sections e U →+* Sections e V where
  toFun s := Sections.ofCompatible e V (restrictedFamily e hVU s) ((restriction_laws e hVU).1 s)
  map_one' := Subtype.ext (restriction_laws e hVU).2.1
  map_mul' s t := Subtype.ext ((restriction_laws e hVU).2.2.1 s t)
  map_zero' := Subtype.ext (restriction_laws e hVU).2.2.2.1
  map_add' s t := Subtype.ext ((restriction_laws e hVU).2.2.2.2 s t)

/-- Restriction is continuous for the inverse-limit topology. -/
theorem continuous_restriction {U V : Opens T} (hVU : V ≤ U) :
    Continuous (restriction e hVU : Sections e U → Sections e V) := sorry

/-- Continuous restriction of sections, bundled as a morphism of topological rings. -/
def restrictionHom {U V : Opens T} (hVU : V ≤ U) :
    TopCommRingCat.of (Sections e U) ⟶ TopCommRingCat.of (Sections e V) :=
  ⟨restriction e hVU, continuous_restriction e hVU⟩

/-- The continuous restrictions satisfy identity and composition laws. -/
theorem structurePresheaf_laws :
    (∀ U : (Opens T)ᵒᵖ,
      restrictionHom e (leOfHom (unop (𝟙 U))) = 𝟙 (TopCommRingCat.of (Sections e (unop U)))) ∧
      (∀ {U V W : (Opens T)ᵒᵖ} (f : U ⟶ V) (g : V ⟶ W),
        restrictionHom e (leOfHom (unop (f ≫ g))) =
          restrictionHom e (leOfHom (unop f)) ≫ restrictionHom e (leOfHom (unop g))) := sorry

/-- The presheaf of topological rings given by compatible quotient-spectrum sections. -/
def structurePresheaf :
    (TopCat.of T).Presheaf TopCommRingCat.{u} where
  obj U := TopCommRingCat.of (Sections e (unop U))
  map f := restrictionHom e (leOfHom (unop f))
  map_id := (structurePresheaf_laws e).1
  map_comp := (structurePresheaf_laws e).2

/-- The objects of the structure presheaf are inverse-limit section rings. -/
theorem structurePresheaf_obj (U : (Opens T)ᵒᵖ) :
    (structurePresheaf e).obj U = TopCommRingCat.of (Sections e (unop U)) := rfl

/-- The maps of the structure presheaf are the continuous restriction homomorphisms. -/
theorem structurePresheaf_map {U V : (Opens T)ᵒᵖ} (f : U ⟶ V) :
    (structurePresheaf e).map f = restrictionHom e (leOfHom (unop f)) := rfl

/-- The inverse-limit structure presheaf satisfies the sheaf condition. -/
theorem structurePresheaf_isSheaf : (structurePresheaf e).IsSheaf := sorry

/-- The sheafed space of open primes equipped with the inverse-limit structure sheaf. -/
def sheafedSpace :
    SheafedSpace TopCommRingCat.{u} where
  carrier := TopCat.of T
  presheaf := structurePresheaf e
  IsSheaf := structurePresheaf_isSheaf e

/-- The underlying ring stalks of a weakly admissible ring's formal spectrum are local. -/
theorem stalk_isLocalRing (hA : TopologicalRing.IsWeaklyAdmissibleRing A) (x : T) :
    IsLocalRing ((LocallyTopologicallyRingedSpaceCat.ringPresheaf (sheafedSpace e)).stalk x) := sorry

end AlgebraicGeometry.McQuillan.FormalSpectrum

namespace AlgebraicGeometry.McQuillan

/-- The weak formal spectrum on a specified homeomorphic presentation of its open primes. -/
def spfOnSpace (A : TopCommRingCat.{u}) (hA : TopologicalRing.IsWeaklyAdmissibleRing A)
    {T : Type u} [TopologicalSpace T]
    (e : T ≃ₜ AlgebraicGeometry.FormalSpectrum.OpenPrime (A : Type u)) :
    LocallyTopologicallyRingedSpaceCat.{u} :=
  LocallyTopologicallyRingedSpaceCat.ofSheafedSpace
    (FormalSpectrum.sheafedSpace e) (FormalSpectrum.stalk_isLocalRing e hA)

/-- The formal spectrum of a weakly admissible topological ring, on its open prime ideals. -/
def spf (A : TopCommRingCat.{u}) (hA : TopologicalRing.IsWeaklyAdmissibleRing A) :
    LocallyTopologicallyRingedSpaceCat.{u} :=
  spfOnSpace A hA (Homeomorph.refl _)

/-- The underlying space of the weak formal spectrum is the space of open primes. -/
theorem spf_obj_carrier (A : TopCommRingCat.{u})
    (hA : TopologicalRing.IsWeaklyAdmissibleRing A) :
    (spf A hA).carrier = TopCat.of (AlgebraicGeometry.FormalSpectrum.OpenPrime (A : Type u)) := rfl

end AlgebraicGeometry.McQuillan
