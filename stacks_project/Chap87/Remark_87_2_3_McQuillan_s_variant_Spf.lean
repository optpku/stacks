/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Spec
public import stacks_project.Chap87.«87_2_0_1_Spf»
public import stacks_project.Chap87.Definition_87_4_8_WeaklyAdmissible
public import stacks_project.Chap87.Remark_87_2_3_McQuillan_s_variant_Neighborhoods

/-!
# Formal spectra of weakly admissible topological rings

McQuillan's `Spf A` is the locally topologically ringed space of open primes of a
weakly admissible topological ring `A`, with structure sheaf the inverse limit of
the pseudo-discrete structure sheaves of `Spec (A ⧸ I)` over weak ideals of
definition `I`.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory Opposite TopCat Topology TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Spec (structureSheaf)
open TopologicalRing

namespace AlgebraicGeometry.McQuillan

namespace OpenPrime

variable {A : Type u} [CommRing A] [TopologicalSpace A]

/-- Send an open prime of `A` to the corresponding prime modulo a weak ideal of
definition. -/
def toQuotient [IsTopologicalRing A] (I : Ideal A)
    (hI : Ideal.IsWeakIdealOfDefinition I) (p : AlgebraicGeometry.OpenPrime A) :
    PrimeSpectrum (A ⧸ I) where
  asIdeal := Ideal.map (Ideal.Quotient.mk I) p.asIdeal
  isPrime := sorry

/-- For a weak ideal of definition `I`, open primes of `A` are homeomorphic to
`Spec (A ⧸ I)`. -/
def homeomorphQuotient [IsTopologicalRing A] (I : Ideal A)
    (hI : Ideal.IsWeakIdealOfDefinition I) :
    AlgebraicGeometry.OpenPrime A ≃ₜ PrimeSpectrum (A ⧸ I) where
  toFun := toQuotient I hI
  invFun := AlgebraicGeometry.OpenPrime.ofQuotient I hI.1
  left_inv := sorry
  right_inv := sorry
  continuous_toFun := sorry
  continuous_invFun := sorry

/-- Forward evaluation of `OpenPrime.homeomorphQuotient`. -/
theorem homeomorphQuotient_apply [IsTopologicalRing A] (I : Ideal A)
    (hI : Ideal.IsWeakIdealOfDefinition I) (p : AlgebraicGeometry.OpenPrime A) :
    homeomorphQuotient I hI p = toQuotient I hI p :=
  sorry

/-- Continuous inverse of `OpenPrime.homeomorphQuotient`, used to transport opens of
McQuillan `Spf A` to opens of `Spec (A ⧸ I)`. -/
def homeomorphQuotientInv [IsTopologicalRing A] (I : Ideal A)
    (hI : Ideal.IsWeakIdealOfDefinition I) :
    C(PrimeSpectrum (A ⧸ I), AlgebraicGeometry.OpenPrime A) :=
  ⟨(homeomorphQuotient I hI).symm, (homeomorphQuotient I hI).continuous_invFun⟩

/-- The underlying function of `OpenPrime.homeomorphQuotientInv` is the inverse
homeomorphism. -/
theorem homeomorphQuotientInv_apply [IsTopologicalRing A] (I : Ideal A)
    (hI : Ideal.IsWeakIdealOfDefinition I) (q : PrimeSpectrum (A ⧸ I)) :
    homeomorphQuotientInv I hI q = (homeomorphQuotient I hI).symm q :=
  sorry

end OpenPrime

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- Transport an open of McQuillan `Spf A` to an open of `Spec (A ⧸ I)` along
`OpenPrime.homeomorphQuotient`. -/
def pullbackOpens (U : Opens (AlgebraicGeometry.OpenPrime A)) (I : Ideal A)
    (hI : Ideal.IsWeakIdealOfDefinition I) : Opens (PrimeSpectrum (A ⧸ I)) :=
  Opens.comap (OpenPrime.homeomorphQuotientInv I hI) U

/-- Sections of `O_Spec(A ⧸ I)` on the transport of `U`. -/
def componentType (U : Opens (AlgebraicGeometry.OpenPrime A)) (I : Ideal A)
    (hI : Ideal.IsWeakIdealOfDefinition I) : Type u :=
  ((structureSheaf (A ⧸ I)).1.obj (op (pullbackOpens U I hI)) : Type u)

/-- Component rings inherit their commutative ring structure from the structure sheaf. -/
instance instCommRingComponentType (U : Opens (AlgebraicGeometry.OpenPrime A)) (I : Ideal A)
    (hI : Ideal.IsWeakIdealOfDefinition I) : CommRing (componentType U I hI) :=
  inferInstanceAs
    (CommRing ((structureSheaf (A ⧸ I)).1.obj (op (pullbackOpens U I hI)) : Type u))

/-- Pseudo-discrete topology on `Γ(U_I, O_Spec(A ⧸ I))`: discrete on compact opens, and
otherwise the initial topology with respect to restrictions to compact opens. -/
@[reducible] def pseudoDiscreteComponentTopology
    (U : Opens (AlgebraicGeometry.OpenPrime A)) (I : Ideal A)
    (hI : Ideal.IsWeakIdealOfDefinition I) : TopologicalSpace (componentType U I hI) :=
  ⨅ (V : Opens (PrimeSpectrum (A ⧸ I))),
    ⨅ (_ : IsCompact (V : Set (PrimeSpectrum (A ⧸ I)))),
      ⨅ (hVU : V ≤ pullbackOpens U I hI),
        TopologicalSpace.induced
          ((structureSheaf (A ⧸ I)).1.map (homOfLE hVU).op).hom
          (⊥ : TopologicalSpace ((structureSheaf (A ⧸ I)).1.obj (op V) : Type u))

/-- The topology on a component ring is the pseudo-discrete topology. -/
instance instTopologicalSpaceComponentType (U : Opens (AlgebraicGeometry.OpenPrime A))
    (I : Ideal A) (hI : Ideal.IsWeakIdealOfDefinition I) :
    TopologicalSpace (componentType U I hI) :=
  pseudoDiscreteComponentTopology U I hI

/-- Restriction of component sections along an inclusion of opens. -/
def componentRestrict {U V : Opens (AlgebraicGeometry.OpenPrime A)} (hVU : V ≤ U)
    (I : Ideal A) (hI : Ideal.IsWeakIdealOfDefinition I) :
    componentType U I hI →+* componentType V I hI :=
  ((structureSheaf (A ⧸ I)).1.map
    (homOfLE
      (Opens.comap_mono (OpenPrime.homeomorphQuotientInv I hI) hVU)).op).hom

/-- The thickening `Spec (A ⧸ J) → Spec (A ⧸ I)` pulls `U_I` back to an open containing
`U_J`. -/
theorem pullbackOpens_subset_comap_factor (U : Opens (AlgebraicGeometry.OpenPrime A))
    {I J : Ideal A} (hI : Ideal.IsWeakIdealOfDefinition I)
    (hJ : Ideal.IsWeakIdealOfDefinition J) (hIJ : I ≤ J) :
    (pullbackOpens U J hJ : Set (PrimeSpectrum (A ⧸ J))) ⊆
      PrimeSpectrum.comap (Ideal.Quotient.factor hIJ) ⁻¹' pullbackOpens U I hI :=
  sorry

/-- Transition maps of the inverse system of structure sheaves along a larger weak
ideal of definition, given by `StructureSheaf.comap` of the quotient factor map. -/
def transition (U : Opens (AlgebraicGeometry.OpenPrime A)) {I J : Ideal A}
    (hI : Ideal.IsWeakIdealOfDefinition I) (hJ : Ideal.IsWeakIdealOfDefinition J)
    (hIJ : I ≤ J) : componentType U I hI →+* componentType U J hJ :=
  StructureSheaf.comap (Ideal.Quotient.factor hIJ)
    (pullbackOpens U I hI) (pullbackOpens U J hJ)
    (pullbackOpens_subset_comap_factor U hI hJ hIJ)

/-- Inverse-limit sections of the pseudo-discrete structure sheaves of `Spec (A ⧸ I)`
over weak ideals of definition. -/
@[ext]
structure Sections (U : Opens (AlgebraicGeometry.OpenPrime A)) where
  /-- Component in `Γ(U_I, O_Spec(A ⧸ I))` for each weak ideal of definition `I`. -/
  component : ∀ I : Ideal A, ∀ hI : Ideal.IsWeakIdealOfDefinition I, componentType U I hI
  /-- Compatibility of components along transitions `A ⧸ I → A ⧸ J`. -/
  compatible : ∀ {I J : Ideal A} (hI : Ideal.IsWeakIdealOfDefinition I)
    (hJ : Ideal.IsWeakIdealOfDefinition J) (hIJ : I ≤ J),
    transition U hI hJ hIJ (component I hI) = component J hJ

/-- Assemble inverse-limit sections from a compatible family of components. -/
def Sections.ofCompatible (U : Opens (AlgebraicGeometry.OpenPrime A))
    (component : ∀ I : Ideal A, ∀ hI : Ideal.IsWeakIdealOfDefinition I,
      componentType U I hI)
    (compatible : ∀ {I J : Ideal A} (hI : Ideal.IsWeakIdealOfDefinition I)
      (hJ : Ideal.IsWeakIdealOfDefinition J) (hIJ : I ≤ J),
      transition U hI hJ hIJ (component I hI) = component J hJ) :
    Sections U :=
  ⟨component, compatible⟩

variable {U : Opens (AlgebraicGeometry.OpenPrime A)}

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
  ⨅ (I : Ideal A), ⨅ (hI : Ideal.IsWeakIdealOfDefinition I),
    TopologicalSpace.induced (fun s ↦ s.component I hI)
      (pseudoDiscreteComponentTopology U I hI)

/-- Inverse-limit section rings are topological rings. -/
instance : IsTopologicalRing (Sections U) := sorry

/-- Restriction of inverse-limit sections along an inclusion of opens. -/
def restriction {V : Opens (AlgebraicGeometry.OpenPrime A)} (hVU : V ≤ U) :
    Sections U →+* Sections V where
  toFun s := ⟨fun I hI ↦ componentRestrict hVU I hI (s.component I hI), sorry⟩
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- Continuity of restriction of inverse-limit sections. -/
theorem continuous_restriction {V : Opens (AlgebraicGeometry.OpenPrime A)} (hVU : V ≤ U) :
    Continuous (restriction hVU : Sections U → Sections V) :=
  sorry

variable (A) in
/-- Structure presheaf of McQuillan `Spf A` with values in topological commutative
rings. -/
def structurePresheaf :
    (TopCat.of (AlgebraicGeometry.OpenPrime A)).Presheaf TopCommRingCat.{u} where
  obj U := TopCommRingCat.of (Sections (unop U))
  map f := ⟨restriction (leOfHom (unop f)), continuous_restriction (leOfHom (unop f))⟩
  map_id _ := sorry
  map_comp _ _ := sorry

variable (A) in
/-- The object of the structure presheaf on an open is the inverse-limit section ring. -/
theorem structurePresheaf_obj (U : (Opens (AlgebraicGeometry.OpenPrime A))ᵒᵖ) :
    (structurePresheaf A).obj U = TopCommRingCat.of (Sections (unop U)) :=
  sorry

variable (A) in
/-- Restriction morphisms of the structure presheaf are `restriction`. -/
theorem structurePresheaf_map {U V : (Opens (AlgebraicGeometry.OpenPrime A))ᵒᵖ} (f : U ⟶ V) :
    (structurePresheaf A).map f =
      ⟨restriction (leOfHom (unop f)), continuous_restriction (leOfHom (unop f))⟩ :=
  sorry

/-- Formal spectrum of a bundled weakly admissible topological commutative ring. -/
def spf (A : TopCommRingCat.{u}) (hA : IsWeaklyAdmissibleRing A) :
    LocallyTopologicallyRingedSpace.{u} :=
  LocallyTopologicallyRingedSpace.ofSheafedSpace
    { carrier := TopCat.of (AlgebraicGeometry.OpenPrime (A : Type u))
      presheaf := @structurePresheaf (A : Type u) inferInstance inferInstance
        hA.toIsTopologicalRing
      IsSheaf := sorry }
    (fun _ ↦ sorry)

/-- The underlying space of McQuillan `spf A` is the space of open primes of `A`. -/
theorem spf_obj_carrier (A : TopCommRingCat.{u}) (hA : IsWeaklyAdmissibleRing A) :
    (spf A hA).carrier = TopCat.of (AlgebraicGeometry.OpenPrime (A : Type u)) :=
  sorry

end AlgebraicGeometry.McQuillan
