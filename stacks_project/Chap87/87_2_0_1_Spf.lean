/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.Topology.Algebra.OpenSubgroup
public import ReasLib.RingTheory.Topology.Adic.Complete
public import stacks_project.Chap87.«87_2_0_1_LocallyTopologicallyRingedSpace»

/-!
# Formal spectra of admissible topological rings

`Spf A` is the locally topologically ringed space of open primes of an admissible topological
ring `A`, with structure sheaf the inverse limit of the pseudo-discrete structure sheaves of
`Spec (A ⧸ I)` over ideals of definition `I`.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory Opposite TopCat Topology TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Spec (structureSheaf)

namespace AlgebraicGeometry

/-- An open prime ideal of a topological ring, viewed as a point of a formal spectrum. -/
structure OpenPrime (A : Type u) [CommRing A] [TopologicalSpace A] where
  /-- Underlying prime of the Zariski spectrum. -/
  toPrimeSpectrum : PrimeSpectrum A
  /-- The prime ideal is open in the ambient topology. -/
  isOpen : IsOpen (toPrimeSpectrum.asIdeal : Set A)

namespace OpenPrime

variable {A : Type u} [CommRing A] [TopologicalSpace A]

/-- The underlying ideal of an open prime. -/
def asIdeal (p : OpenPrime A) : Ideal A :=
  p.toPrimeSpectrum.asIdeal

/-- Subspace topology inherited from `PrimeSpectrum A`. -/
instance : TopologicalSpace (OpenPrime A) :=
  TopologicalSpace.induced toPrimeSpectrum inferInstance

/-- The open prime of `A` corresponding to a prime of `A ⧸ I` when `I` is open. -/
def ofQuotient [IsTopologicalRing A] (I : Ideal A) (hI : IsOpen (I : Set A))
    (q : PrimeSpectrum (A ⧸ I)) : OpenPrime A where
  toPrimeSpectrum := PrimeSpectrum.comap (Ideal.Quotient.mk I) q
  isOpen := sorry

/-- `OpenPrime.ofQuotient` as a continuous map. -/
def ofQuotientContinuous [IsTopologicalRing A] (I : Ideal A) (hI : IsOpen (I : Set A)) :
    C(PrimeSpectrum (A ⧸ I), OpenPrime A) where
  toFun := ofQuotient I hI
  continuous_toFun := sorry

/-- Pull back an open prime along a continuous ring homomorphism. -/
def comap {B : Type u} [CommRing B] [TopologicalSpace B] (φ : A →+* B) (hφ : Continuous φ)
    (p : OpenPrime B) : OpenPrime A where
  toPrimeSpectrum := PrimeSpectrum.comap φ p.toPrimeSpectrum
  isOpen := Ideal.coe_comap φ p.asIdeal ▸ p.isOpen.preimage hφ

/-- Continuity of `OpenPrime.comap`. -/
theorem continuous_comap {B : Type u} [CommRing B] [TopologicalSpace B] (φ : A →+* B)
    (hφ : Continuous φ) : Continuous (comap φ hφ) :=
  sorry

/-- Send an open prime of `A` to the corresponding prime modulo an ideal of definition. -/
def toQuotient [IsTopologicalRing A] (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (p : OpenPrime A) : PrimeSpectrum (A ⧸ I) where
  asIdeal := Ideal.map (Ideal.Quotient.mk I) p.asIdeal
  isPrime := sorry

/-- For an ideal of definition `I`, open primes of `A` are homeomorphic to `Spec (A ⧸ I)`. -/
def homeomorphQuotient [IsTopologicalRing A] (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    OpenPrime A ≃ₜ PrimeSpectrum (A ⧸ I) where
  toFun := toQuotient I hI
  invFun := ofQuotient I hI.1
  left_inv := sorry
  right_inv := sorry
  continuous_toFun := sorry
  continuous_invFun := sorry

/-- Continuous inverse of `OpenPrime.homeomorphQuotient`, used to transport opens of `Spf A`
to opens of `Spec (A ⧸ I)`. -/
def homeomorphQuotientInv [IsTopologicalRing A] (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    C(PrimeSpectrum (A ⧸ I), OpenPrime A) :=
  ⟨(homeomorphQuotient I hI).symm, (homeomorphQuotient I hI).continuous_invFun⟩

/-- The underlying function of `OpenPrime.homeomorphQuotientInv` is the inverse homeomorphism. -/
theorem homeomorphQuotientInv_apply [IsTopologicalRing A] (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (q : PrimeSpectrum (A ⧸ I)) :
    homeomorphQuotientInv I hI q = (homeomorphQuotient I hI).symm q :=
  sorry

end OpenPrime

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- Transport an open of `Spf A` to an open of `Spec (A ⧸ I)` along
`OpenPrime.homeomorphQuotient`. -/
def pullbackOpens (U : Opens (OpenPrime A)) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    Opens (PrimeSpectrum (A ⧸ I)) :=
  Opens.comap (OpenPrime.homeomorphQuotientInv I hI) U

/-- Sections of `O_Spec(A ⧸ I)` on the transport of `U`. -/
def componentType (U : Opens (OpenPrime A)) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) : Type u :=
  ((structureSheaf (A ⧸ I)).1.obj (op (pullbackOpens U I hI)) : Type u)

/-- Component rings inherit their commutative ring structure from the structure sheaf. -/
instance instCommRingComponentType (U : Opens (OpenPrime A)) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) : CommRing (componentType U I hI) :=
  inferInstanceAs
    (CommRing ((structureSheaf (A ⧸ I)).1.obj (op (pullbackOpens U I hI)) : Type u))

/-- Pseudo-discrete topology on `Γ(U_I, O_Spec(A ⧸ I))`: discrete on compact opens, and
otherwise the initial topology with respect to restrictions to compact opens. -/
@[reducible] def pseudoDiscreteComponentTopology (U : Opens (OpenPrime A)) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    TopologicalSpace (componentType U I hI) :=
  ⨅ (V : Opens (PrimeSpectrum (A ⧸ I))),
    ⨅ (_ : IsCompact (V : Set (PrimeSpectrum (A ⧸ I)))),
      ⨅ (hVU : V ≤ pullbackOpens U I hI),
        TopologicalSpace.induced
          ((structureSheaf (A ⧸ I)).1.map (homOfLE hVU).op).hom
          (⊥ : TopologicalSpace ((structureSheaf (A ⧸ I)).1.obj (op V) : Type u))

/-- The topology on a component ring is the pseudo-discrete topology. -/
instance instTopologicalSpaceComponentType (U : Opens (OpenPrime A)) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    TopologicalSpace (componentType U I hI) :=
  pseudoDiscreteComponentTopology U I hI

/-- Compact opens of `Spec (A ⧸ I)` carry the discrete topology on pseudo-discrete sections. -/
theorem isDiscrete_componentType_of_isCompact (U : Opens (OpenPrime A)) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hU : IsCompact ((pullbackOpens U I hI : Set (PrimeSpectrum (A ⧸ I))))) :
    DiscreteTopology (componentType U I hI) :=
  sorry

/-- Restriction of component sections along an inclusion of opens. -/
def componentRestrict {U V : Opens (OpenPrime A)} (hVU : V ≤ U) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    componentType U I hI →+* componentType V I hI :=
  ((structureSheaf (A ⧸ I)).1.map
    (homOfLE (Opens.comap_mono (OpenPrime.homeomorphQuotientInv I hI) hVU)).op).hom

/-- The thickening `Spec (A ⧸ J) → Spec (A ⧸ I)` pulls `U_I` back to an open containing `U_J`. -/
theorem pullbackOpens_subset_comap_factor (U : Opens (OpenPrime A)) {I J : Ideal A}
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hJ : TopologicalRing.Ideal.IsIdealOfDefinition J) (hIJ : I ≤ J) :
    (pullbackOpens U J hJ : Set (PrimeSpectrum (A ⧸ J))) ⊆
      PrimeSpectrum.comap (Ideal.Quotient.factor hIJ) ⁻¹' pullbackOpens U I hI :=
  sorry

/-- Transition maps of the inverse system of structure sheaves along a larger ideal of
definition, given by `StructureSheaf.comap` of the quotient factor map. -/
def transition (U : Opens (OpenPrime A)) {I J : Ideal A}
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hJ : TopologicalRing.Ideal.IsIdealOfDefinition J) (hIJ : I ≤ J) :
    componentType U I hI →+* componentType U J hJ :=
  StructureSheaf.comap (Ideal.Quotient.factor hIJ)
    (pullbackOpens U I hI) (pullbackOpens U J hJ)
    (pullbackOpens_subset_comap_factor U hI hJ hIJ)

namespace Spf

/-- Inverse-limit sections of the pseudo-discrete structure sheaves of `Spec (A ⧸ I)` over
ideals of definition. -/
@[ext]
structure Sections (U : Opens (OpenPrime A)) where
  /-- Component in `Γ(U_I, O_Spec(A ⧸ I))` for each ideal of definition `I`. -/
  component : ∀ I : Ideal A, ∀ hI : TopologicalRing.Ideal.IsIdealOfDefinition I,
    componentType U I hI
  /-- Compatibility of components along transitions `A ⧸ I → A ⧸ J`. -/
  compatible : ∀ {I J : Ideal A} (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hJ : TopologicalRing.Ideal.IsIdealOfDefinition J) (hIJ : I ≤ J),
    transition U hI hJ hIJ (component I hI) = component J hJ

/-- Assemble inverse-limit sections from a compatible family of components. -/
def ofCompatible (U : Opens (OpenPrime A))
    (component : ∀ I : Ideal A, ∀ hI : TopologicalRing.Ideal.IsIdealOfDefinition I,
      componentType U I hI)
    (compatible : ∀ {I J : Ideal A} (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
      (hJ : TopologicalRing.Ideal.IsIdealOfDefinition J) (hIJ : I ≤ J),
      transition U hI hJ hIJ (component I hI) = component J hJ) :
    Sections U :=
  ⟨component, compatible⟩

variable {U : Opens (OpenPrime A)}

/-- Zero inverse-limit section. -/
instance : Zero (Sections U) where
  zero := ⟨fun _ _ ↦ 0, sorry⟩

/-- Unit inverse-limit section. -/
instance : One (Sections U) where
  one := ⟨fun _ _ ↦ 1, sorry⟩

/-- Pointwise addition of inverse-limit sections. -/
instance : Add (Sections U) where
  add x y := ⟨fun I hI ↦ x.component I hI + y.component I hI, sorry⟩

/-- Pointwise negation of inverse-limit sections. -/
instance : Neg (Sections U) where
  neg x := ⟨fun I hI ↦ -x.component I hI, sorry⟩

/-- Pointwise subtraction of inverse-limit sections. -/
instance : Sub (Sections U) where
  sub x y := ⟨fun I hI ↦ x.component I hI - y.component I hI, sorry⟩

/-- Pointwise multiplication of inverse-limit sections. -/
instance : Mul (Sections U) where
  mul x y := ⟨fun I hI ↦ x.component I hI * y.component I hI, sorry⟩

/-- Natural-number scalar multiplication of inverse-limit sections. -/
instance : SMul ℕ (Sections U) where
  smul n x := ⟨fun I hI ↦ n • x.component I hI, sorry⟩

/-- Integer scalar multiplication of inverse-limit sections. -/
instance : SMul ℤ (Sections U) where
  smul n x := ⟨fun I hI ↦ n • x.component I hI, sorry⟩

/-- Natural-number powers of inverse-limit sections. -/
instance : Pow (Sections U) ℕ where
  pow x n := ⟨fun I hI ↦ x.component I hI ^ n, sorry⟩

/-- Canonical map from `ℕ` into inverse-limit sections. -/
instance : NatCast (Sections U) where
  natCast n := ⟨fun _ _ ↦ n, sorry⟩

/-- Canonical map from `ℤ` into inverse-limit sections. -/
instance : IntCast (Sections U) where
  intCast n := ⟨fun _ _ ↦ n, sorry⟩

/-- Inverse-limit sections form a commutative ring. -/
instance : CommRing (Sections U) where
  add := Add.add
  zero := Zero.zero
  neg := Neg.neg
  sub := Sub.sub
  mul := Mul.mul
  one := One.one
  nsmul := SMul.smul
  zsmul := SMul.smul
  npow := fun n x ↦ Pow.pow x n
  natCast := Nat.cast
  intCast := Int.cast
  add_assoc := sorry
  zero_add := sorry
  add_zero := sorry
  nsmul_zero := sorry
  nsmul_succ := sorry
  neg_add_cancel := sorry
  add_comm := sorry
  sub_eq_add_neg := sorry
  zsmul_zero' := sorry
  zsmul_succ' := sorry
  zsmul_neg' := sorry
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry
  npow_zero := sorry
  npow_succ := sorry
  left_distrib := sorry
  right_distrib := sorry
  mul_comm := sorry
  zero_mul := sorry
  mul_zero := sorry
  natCast_zero := sorry
  natCast_succ := sorry
  intCast_ofNat := sorry
  intCast_negSucc := sorry

/-- Inverse-limit topology on sections, initial with respect to the projections onto
pseudo-discrete component rings. -/
instance : TopologicalSpace (Sections U) :=
  ⨅ (I : Ideal A), ⨅ (hI : TopologicalRing.Ideal.IsIdealOfDefinition I),
    TopologicalSpace.induced (fun s ↦ s.component I hI)
      (pseudoDiscreteComponentTopology U I hI)

/-- Inverse-limit section rings are topological rings. -/
instance : IsTopologicalRing (Sections U) := sorry

/-- Restriction of inverse-limit sections along an inclusion of opens. -/
def restriction {V : Opens (OpenPrime A)} (hVU : V ≤ U) : Sections U →+* Sections V where
  toFun s :=
    ⟨fun I hI ↦ componentRestrict hVU I hI (s.component I hI), sorry⟩
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- Continuity of restriction of inverse-limit sections. -/
theorem continuous_restriction {V : Opens (OpenPrime A)} (hVU : V ≤ U) :
    Continuous (restriction hVU : Sections U → Sections V) :=
  sorry

variable (A) in
/-- Structure presheaf of `Spf A` with values in topological commutative rings. -/
def structurePresheaf : (TopCat.of (OpenPrime A)).Presheaf TopCommRingCat.{u} where
  obj U := TopCommRingCat.of (Sections (unop U))
  map f := ⟨restriction (leOfHom (unop f)), continuous_restriction (leOfHom (unop f))⟩
  map_id _ := sorry
  map_comp _ _ := sorry

variable (A) in
/-- The object of the structure presheaf on an open is the inverse-limit section ring. -/
theorem structurePresheaf_obj (U : (Opens (OpenPrime A))ᵒᵖ) :
    (structurePresheaf A).obj U = TopCommRingCat.of (Sections (unop U)) :=
  sorry

variable (A) in
/-- Restriction morphisms of the structure presheaf are `Spf.restriction`. -/
theorem structurePresheaf_map {U V : (Opens (OpenPrime A))ᵒᵖ} (f : U ⟶ V) :
    (structurePresheaf A).map f =
      ⟨restriction (leOfHom (unop f)), continuous_restriction (leOfHom (unop f))⟩ :=
  sorry

variable (A) in
/-- Canonical cone from `A` to the inverse system of quotients by ideals of definition. -/
def quotientCone :
    A → ∀ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I → A ⧸ I :=
  fun a I _ ↦ Ideal.Quotient.mk I a

variable (A) in
/-- Evaluation of the quotient cone at an ideal of definition. -/
theorem quotientCone_apply (a : A) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    quotientCone A a I hI = Ideal.Quotient.mk I a :=
  sorry

variable (A) in
/-- Canonical ring homomorphism from `A ⧸ I` to a component of global sections. -/
def quotientToComponent (I : Ideal A) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    A ⧸ I →+* componentType (⊤ : Opens (OpenPrime A)) I hI :=
  algebraMap (A ⧸ I)
    ((structureSheaf (A ⧸ I)).1.obj
      (op (pullbackOpens (⊤ : Opens (OpenPrime A)) I hI)))

variable (A) in
/-- `Spf.quotientToComponent` is the canonical algebra map into structure sheaf sections. -/
theorem quotientToComponent_apply (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (x : A ⧸ I) :
    quotientToComponent A I hI x =
      algebraMap (A ⧸ I)
        ((structureSheaf (A ⧸ I)).1.obj
          (op (pullbackOpens (⊤ : Opens (OpenPrime A)) I hI))) x :=
  sorry

variable (A) in
/-- Inverse of `A ⧸ I → Γ(U_I, O_Spec(A ⧸ I))` on global sections, given by
`StructureSheaf.globalSectionsIso.inv`, using `pullbackOpens ⊤ = ⊤`. -/
def componentToQuotient (I : Ideal A) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    componentType (⊤ : Opens (OpenPrime A)) I hI →+* A ⧸ I :=
  (StructureSheaf.globalSectionsIso (A ⧸ I)).inv.hom

variable (A) in
/-- `Spf.componentToQuotient` inverts `Spf.quotientToComponent` on the image of the cone. -/
theorem quotientToComponent_componentToQuotient (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (x : A ⧸ I) :
    componentToQuotient A I hI (quotientToComponent A I hI x) = x :=
  sorry

variable (A) in
/-- Underlying function of `Spf.componentToQuotient`. -/
theorem componentToQuotient_apply (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (s : componentType (⊤ : Opens (OpenPrime A)) I hI) :
    componentToQuotient A I hI s = (StructureSheaf.globalSectionsIso (A ⧸ I)).inv.hom s :=
  sorry

variable (A) in
/-- Canonical ring homomorphism from `A` to global sections of `Spf A`, the cone to the
inverse limit of `A ⧸ I`. -/
def globalSectionsHom : A →+* Sections (⊤ : Opens (OpenPrime A)) where
  toFun a :=
    ⟨fun I hI ↦ quotientToComponent A I hI (Ideal.Quotient.mk I a), sorry⟩
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

variable (A) in
/-- Projection of a global section to the inverse system `A ⧸ I`. -/
def sectionsToQuotients (s : Sections (⊤ : Opens (OpenPrime A))) :
    ∀ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I → A ⧸ I :=
  fun I hI ↦ componentToQuotient A I hI (s.component I hI)

variable (A) in
/-- Evaluation of `Spf.sectionsToQuotients` at an ideal of definition. -/
theorem sectionsToQuotients_apply (s : Sections (⊤ : Opens (OpenPrime A)))
    (I : Ideal A) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    sectionsToQuotients A s I hI = componentToQuotient A I hI (s.component I hI) :=
  sorry

variable (A) in
/-- Unique two-sided inverse of the global-sections cone `A → lim A ⧸ I`, characterized by
`Ideal.Quotient.mk I (inv s) = componentToQuotient (s.component I)`. -/
def globalSectionsInvHom [TopologicalRing.IsAdmissibleRing A] :
    Sections (⊤ : Opens (OpenPrime A)) →+* A where
  toFun s :=
    Classical.epsilon fun a : A ↦
      ∀ (I : Ideal A) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I),
        Ideal.Quotient.mk I a = componentToQuotient A I hI (s.component I hI)
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

variable (A) in
/-- `Spf.globalSectionsHom` is bijective. -/
theorem globalSectionsHom_bijective [TopologicalRing.IsAdmissibleRing A] :
    Function.Bijective (globalSectionsHom A) :=
  sorry

variable (A) in
/-- `Spf.globalSectionsHom` is continuous for the inverse-limit topology. -/
theorem globalSectionsHom_continuous : Continuous (globalSectionsHom A) :=
  sorry

variable (A) in
/-- The inverse global-sections comparison is continuous. -/
theorem globalSectionsInvHom_continuous [TopologicalRing.IsAdmissibleRing A] :
    Continuous (globalSectionsInvHom A) :=
  sorry

variable (A) in
/-- The inverse of the global-sections cone recovers every quotient component. -/
theorem globalSectionsInvHom_mk [TopologicalRing.IsAdmissibleRing A]
    (s : Sections (⊤ : Opens (OpenPrime A)))
    (I : Ideal A) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    Ideal.Quotient.mk I (globalSectionsInvHom A s) =
      componentToQuotient A I hI (s.component I hI) :=
  sorry

end Spf

variable (A) in
/-- Formal spectrum of an admissible topological ring. -/
def Spf [TopologicalRing.IsAdmissibleRing A] : LocallyTopologicallyRingedSpace.{u} :=
  LocallyTopologicallyRingedSpace.ofSheafedSpace
    { carrier := TopCat.of (OpenPrime A)
      presheaf := Spf.structurePresheaf A
      IsSheaf := sorry }
    (fun _ ↦ sorry)

namespace Spf

/-- Underlying continuous map of spaces induced by a continuous ring homomorphism. -/
def mapBase {B : Type u} [CommRing B] [TopologicalSpace B] (φ : A →+* B) (hφ : Continuous φ) :
    TopCat.of (OpenPrime B) ⟶ TopCat.of (OpenPrime A) :=
  TopCat.ofHom ⟨OpenPrime.comap φ hφ, OpenPrime.continuous_comap φ hφ⟩

/-- The map `Spec (B ⧸ J) → Spec (A ⧸ I)` pulls `U_I` back to an open containing the transport
of `φ⁻¹ U`, whenever `I ≤ φ⁻¹(J)`. -/
theorem pullbackOpens_subset_comap_quotient {B : Type u} [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] (φ : A →+* B) (hφ : Continuous φ) (U : Opens (OpenPrime A))
    {I : Ideal A} {J : Ideal B}
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hJ : TopologicalRing.Ideal.IsIdealOfDefinition J) (hIJ : I ≤ Ideal.comap φ J) :
    (pullbackOpens (Opens.comap ⟨OpenPrime.comap φ hφ, OpenPrime.continuous_comap φ hφ⟩ U)
        J hJ : Set (PrimeSpectrum (B ⧸ J))) ⊆
      PrimeSpectrum.comap (Ideal.quotientMap J φ hIJ) ⁻¹' pullbackOpens U I hI :=
  sorry

/-- For `I ≤ φ⁻¹(J)`, the component map induced by `A ⧸ I → B ⧸ J`, given by
`StructureSheaf.comap`. -/
def componentMapOfLe {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (φ : A →+* B) (hφ : Continuous φ) (U : Opens (OpenPrime A)) {I : Ideal A} {J : Ideal B}
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hJ : TopologicalRing.Ideal.IsIdealOfDefinition J) (hIJ : I ≤ Ideal.comap φ J) :
    componentType U I hI →+*
      componentType (Opens.comap ⟨OpenPrime.comap φ hφ, OpenPrime.continuous_comap φ hφ⟩ U) J hJ :=
  StructureSheaf.comap (Ideal.quotientMap J φ hIJ) (pullbackOpens U I hI)
    (pullbackOpens (Opens.comap ⟨OpenPrime.comap φ hφ, OpenPrime.continuous_comap φ hφ⟩ U) J hJ)
    (pullbackOpens_subset_comap_quotient φ hφ U hI hJ hIJ)

/-- Inverse-limit sheaf map induced by a continuous ring homomorphism. The `J`-component is the
unique section agreeing with `componentMapOfLe` for every ideal of definition `I ≤ φ⁻¹(J)`. -/
def sectionsMap {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [TopologicalRing.IsAdmissibleRing A] [TopologicalRing.IsAdmissibleRing B]
    (φ : A →+* B) (hφ : Continuous φ) (U : Opens (OpenPrime A)) :
    Sections U →+* Sections (Opens.comap ⟨OpenPrime.comap φ hφ, OpenPrime.continuous_comap φ hφ⟩ U)
    where
  toFun s :=
    ⟨fun J hJ ↦
      Classical.epsilon fun t ↦
        ∀ (I : Ideal A) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
          (hIJ : I ≤ Ideal.comap φ J),
          t = componentMapOfLe φ hφ U hI hJ hIJ (s.component I hI),
      sorry⟩
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- The `J`-component of `Spf.sectionsMap` equals `componentMapOfLe` for every ideal of
definition `I ≤ φ⁻¹(J)`. -/
theorem sectionsMap_apply_of_le {B : Type u} [CommRing B] [TopologicalSpace B]
    [TopologicalRing.IsAdmissibleRing A] [TopologicalRing.IsAdmissibleRing B]
    [IsTopologicalRing B] (φ : A →+* B) (hφ : Continuous φ) (U : Opens (OpenPrime A))
    {I : Ideal A} {J : Ideal B}
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hJ : TopologicalRing.Ideal.IsIdealOfDefinition J) (hIJ : I ≤ Ideal.comap φ J)
    (s : Sections U) :
    (sectionsMap φ hφ U s).component J hJ =
      componentMapOfLe φ hφ U hI hJ hIJ (s.component I hI) :=
  sorry

/-- Continuity of `Spf.sectionsMap`. -/
theorem continuous_sectionsMap {B : Type u} [CommRing B] [TopologicalSpace B]
    [TopologicalRing.IsAdmissibleRing A] [TopologicalRing.IsAdmissibleRing B]
    [IsTopologicalRing B] (φ : A →+* B) (hφ : Continuous φ) (U : Opens (OpenPrime A)) :
    Continuous (sectionsMap φ hφ U) :=
  sorry

variable [TopologicalRing.IsAdmissibleRing A]

/-- A continuous homomorphism of admissible rings sends an ideal of definition of the target
into a neighborhood of zero that contains some ideal of definition of the source. -/
theorem exists_isIdealOfDefinition_le_comap {B : Type u} [CommRing B] [TopologicalSpace B]
    [TopologicalRing.IsAdmissibleRing B]
    (φ : A →+* B) (hφ : Continuous φ) {J : Ideal B}
    (hJ : TopologicalRing.Ideal.IsIdealOfDefinition J) :
    ∃ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I ∧ I ≤ Ideal.comap φ J :=
  sorry

/-- Contravariant map of affine formal spectra induced by a continuous ring homomorphism. -/
def map {B : Type u} [CommRing B] [TopologicalSpace B] [TopologicalRing.IsAdmissibleRing B]
    (φ : A →+* B) (hφ : Continuous φ) :
    LocallyTopologicallyRingedSpace.Hom (Spf B) (Spf A) where
  toSheafedHom :=
    SheafedSpace.fullyFaithfulForgetToPresheafedSpace.preimage
      { base := mapBase φ hφ
        c :=
          { app := fun U ↦ ⟨sectionsMap φ hφ (unop U), continuous_sectionsMap φ hφ (unop U)⟩
            naturality := fun _ _ _ ↦ sorry } }
  isLocalHom := fun _ ↦ sorry

/-- Continuity of the underlying ring homomorphism of `Spf.map`. -/
theorem map_continuous {B : Type u} [CommRing B] [TopologicalSpace B]
    [TopologicalRing.IsAdmissibleRing B] (φ : A →+* B) (hφ : Continuous φ) :
    Continuous φ :=
  hφ

/-- `Spf.map` is contravariant in the ring homomorphism. -/
theorem map_comp {B C : Type u} [CommRing B] [TopologicalSpace B]
    [TopologicalRing.IsAdmissibleRing B] [CommRing C] [TopologicalSpace C]
    [TopologicalRing.IsAdmissibleRing C] (φ : A →+* B) (hφ : Continuous φ) (ψ : B →+* C)
    (hψ : Continuous ψ) :
    LocallyTopologicallyRingedSpace.comp (map ψ hψ) (map φ hφ) =
      map (ψ.comp φ) (hψ.comp hφ) :=
  sorry

/-- Extract a continuous ring homomorphism from a morphism of affine formal spectra. -/
def homToContinuous {B : Type u} [CommRing B] [TopologicalSpace B]
    [TopologicalRing.IsAdmissibleRing B]
    (f : LocallyTopologicallyRingedSpace.Hom (Spf B) (Spf A)) :
    TopCommRingCat.of A ⟶ TopCommRingCat.of B :=
  ⟨(globalSectionsInvHom B).comp
      ((f.toSheafedHom.hom.c.app (op ⊤)).1.comp (globalSectionsHom A)),
    sorry⟩

/-- Morphisms of affine formal spectra in LTRS are identified with continuous ring
homomorphisms. -/
def homEquiv {B : Type u} [CommRing B] [TopologicalSpace B]
    [TopologicalRing.IsAdmissibleRing B] :
    LocallyTopologicallyRingedSpace.Hom (Spf B) (Spf A) ≃
      (TopCommRingCat.of A ⟶ TopCommRingCat.of B) where
  toFun := homToContinuous
  invFun φ := map φ.1 φ.2
  left_inv := sorry
  right_inv := sorry

/-- Forward evaluation of `Spf.homEquiv`. -/
theorem homEquiv_apply {B : Type u} [CommRing B] [TopologicalSpace B]
    [TopologicalRing.IsAdmissibleRing B]
    (f : LocallyTopologicallyRingedSpace.Hom (Spf B) (Spf A)) :
    homEquiv f = homToContinuous f :=
  sorry

end Spf

end AlgebraicGeometry
