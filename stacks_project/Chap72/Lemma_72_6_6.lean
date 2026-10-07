module

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import Mathlib.Topology.LocallyFinite
public import ReasLib.RingTheory.Localization.TotalQuotient
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_47_3_RationalFunction
public import stacks_project.Chap68.Definition_68_11_7_HenselianLocalRing
public import stacks_project.Chap72.Definition_72_6_2_Prime

/-!
# Local finiteness of vanishing and poles of rational units

On a locally Noetherian integral algebraic space, a rational unit is regular
outside a locally finite collection of prime divisors, and has nonzero order of
vanishing on a locally finite collection of prime divisors.

The comparison `R(X) ⟶ Q(O_{X, ξ}^h)` is reconstructed on the Definition 72.6.2
`PrimeDivisor` owner: `Lemma_72_6_3` lives in an incompatible `IsIntegral` universe.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry nonZeroDivisors

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- A morphism of algebraic spaces preserves dense opens when the pullback of every
dense open subspace remains dense. -/
def PreservesDenseOpens {X Y : AlgebraicSpace S} (f : Y ⟶ X) : Prop :=
  ∀ (U : smallZariskiSite X), IsDense U.hom → IsDense (domainInfFst f U.hom)

/-- The structure morphism of an elementary étale neighbourhood preserves dense opens. -/
theorem preservesDenseOpens_of_elementary {X : AlgebraicSpace S} {x : Points X}
    (U : EtaleNeighborhood.Elementary X x) : PreservesDenseOpens U.obj.hom :=
  sorry

/-- The fibre product of an open immersion along an arbitrary morphism remains an
open immersion. -/
theorem isOpenImmersion_domainInfFst {X Y : AlgebraicSpace S} {f : Y ⟶ X}
    (U : smallZariskiSite X) :
    IsOpenImmersion (domainInfFst f U.hom) :=
  sorry

/-- Pull back a partial map along a morphism that preserves dense opens, using the
fibre product of the domain with the source. -/
def PartialMap.precomp {X Y Z : AlgebraicSpace S} (φ : PartialMap X Z) {f : Y ⟶ X}
    (hf : PreservesDenseOpens f) : PartialMap Y Z where
  domain :=
    MorphismProperty.Over.mk ⊤ (domainInfFst f φ.domain.hom)
      (isOpenImmersion_domainInfFst φ.domain)
  dense_domain := hf φ.domain φ.dense_domain
  hom := domainInfSnd f φ.domain.hom ≫ φ.hom

/-- Precomposition of equivalent partial maps yields equivalent partial maps. -/
theorem PartialMap.precomp_toRationalMap_respects {X Y : AlgebraicSpace S}
    {f : Y ⟶ X} (hf : PreservesDenseOpens f)
    {φ ψ : PartialMap X (affineLine S)} (h : PartialMap.equiv φ ψ) :
    (φ.precomp hf).toRationalMap = (ψ.precomp hf).toRationalMap :=
  sorry

/-- Pull back rational functions along a morphism that preserves dense opens. -/
def rationalFunctionComap {X Y : AlgebraicSpace S} {f : Y ⟶ X}
    (hf : PreservesDenseOpens f) : RationalFunction X →+* RationalFunction Y where
  toFun :=
    Quotient.lift (fun ψ : PartialMap X (affineLine S) ↦ (ψ.precomp hf).toRationalMap)
      (fun _ _ ↦ PartialMap.precomp_toRationalMap_respects hf)
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- Global sections of a scheme over `S`, viewed as rational functions on the
associated algebraic space. -/
def sectionsToRationalFunction (T : Over S) :
    Γ(T.left, ⊤) →+* RationalFunction (ofOver T) where
  toFun s := (PartialMap.ofHom (ofOverMap (homOfCoord T s))).toRationalMap
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- Nonzerodivisors of global sections become units in the rational-function ring. -/
theorem isUnit_sectionsToRationalFunction (T : Over S)
    (y : nonZeroDivisors Γ(T.left, ⊤)) :
    IsUnit (sectionsToRationalFunction T y) :=
  sorry

/-- The total quotient ring of global sections of a scheme over `S` maps to the
rational-function ring of the associated algebraic space. -/
def sectionsFractionsToRationalFunction (T : Over S) :
    FractionRing Γ(T.left, ⊤) →+* RationalFunction (ofOver T) :=
  IsLocalization.lift (isUnit_sectionsToRationalFunction T)

/-- The colimit coprojection `henselianLocalRing.ι` sends nonzerodivisors to
nonzerodivisors. -/
theorem henselianLocalRing.ι_maps_nonZeroDivisors {X : AlgebraicSpace S} [IsDecent X]
    {x : Points X} (U : EtaleNeighborhood.Elementary X x) :
    nonZeroDivisors Γ((EtaleNeighborhood.Elementary.toScheme X x).obj U, ⊤) ≤
      Submonoid.comap (henselianLocalRing.ι X x U)
        (nonZeroDivisors (henselianLocalRing X x)) :=
  sorry

variable {X : AlgebraicSpace S} [IsLocallyNoetherian X] [IsIntegral X]

/-- There is an elementary étale neighbourhood of `ξ` on which the comparison from
the total quotient ring of global sections to rational functions is bijective. -/
theorem exists_elementary_sectionsFractions_bijective (Z : ClosedSubspace X)
    [IsIntegral Z.X] {ξ : Points X} (hξ : IsGenericPoint ξ Z.pointsSet)
    (hcodim : localRingDimAt ξ = 1) :
    ∃ U : EtaleNeighborhood.Elementary X ξ,
      Function.Bijective (sectionsFractionsToRationalFunction U.obj.toOver) :=
  sorry

/-- The identification of `R(U)` with `Q(Γ(U, ⊤))` on an elementary neighbourhood
where the comparison is bijective. -/
def neighbourhoodFractionsEquiv {ξ : Points X} (U : EtaleNeighborhood.Elementary X ξ)
    (hU : Function.Bijective (sectionsFractionsToRationalFunction U.obj.toOver)) :
    FractionRing Γ((EtaleNeighborhood.Elementary.toScheme X ξ).obj U, ⊤) ≃+*
      RationalFunction (ofOver U.obj.toOver) :=
  RingEquiv.ofBijective (sectionsFractionsToRationalFunction U.obj.toOver) hU

/-- Canonical ring map `R(X) ⟶ Q(O_{X, ξ}^h)` from the function field of `X` to
the total ring of fractions of the henselian local ring at a codimension-one
point. -/
def ClosedSubspace.functionFieldToHenselianFraction (Z : ClosedSubspace X) [IsIntegral Z.X]
    {ξ : Points X} (hξ : IsGenericPoint ξ Z.pointsSet)
    (hcodim : localRingDimAt ξ = 1) :
    RationalFunction X →+* FractionRing (henselianLocalRing X ξ) :=
  let U := Classical.choose (exists_elementary_sectionsFractions_bijective Z hξ hcodim)
  let hU :=
    Classical.choose_spec (exists_elementary_sectionsFractions_bijective Z hξ hcodim)
  (Localization.totalQuotientMap (henselianLocalRing.ι X ξ U)
      (henselianLocalRing.ι_maps_nonZeroDivisors U)).comp
    ((neighbourhoodFractionsEquiv U hU).symm.toRingHom.comp
      (rationalFunctionComap (preservesDenseOpens_of_elementary U)))

namespace PrimeDivisor

/-- Canonical embedding of the function field into the total quotient ring of the
henselian local ring at the generic point of a prime divisor. -/
def functionFieldToHenselianFraction (Z : PrimeDivisor X) :
    RationalFunction X →+* FractionRing (henselianLocalRing X Z.genericPoint) :=
  ClosedSubspace.functionFieldToHenselianFraction
    (ClosedSubspace.ofIrreducibleClosed Z.support)
    ((ClosedSubspace.pointsSet_ofIrreducibleClosed Z.support).symm ▸
      isGenericPoint_pointsEquivIrreducibleCloseds_symm Z.support)
    Z.localRingDimAt_genericPoint

/-- Membership of a rational function in the image of `O_{X, ξ}^h` inside
`Q(O_{X, ξ}^h)`, recovering the source phrase `f ∈ O_{X, ξ}`. -/
def mem_henselianLocalRing (Z : PrimeDivisor X) (f : RationalFunction X) : Prop :=
  functionFieldToHenselianFraction Z f ∈
    Set.range
      (algebraMap (henselianLocalRing X Z.genericPoint)
        (FractionRing (henselianLocalRing X Z.genericPoint)))

/-- Unfolding form of `mem_henselianLocalRing`. -/
theorem mem_henselianLocalRing_iff (Z : PrimeDivisor X) (f : RationalFunction X) :
    mem_henselianLocalRing Z f ↔
      ∃ a : henselianLocalRing X Z.genericPoint,
        algebraMap (henselianLocalRing X Z.genericPoint)
            (FractionRing (henselianLocalRing X Z.genericPoint)) a =
          functionFieldToHenselianFraction Z f :=
  sorry

/-- The order of vanishing of a rational unit along a prime divisor, as the
length difference of a nonzerodivisor representation of its image under
`functionFieldToHenselianFraction`. -/
def ord (Z : PrimeDivisor X) (f : (RationalFunction X)ˣ) : ℤ :=
  let A := henselianLocalRing X Z.genericPoint
  let ab :=
    IsLocalization.sec (nonZeroDivisors A)
      (functionFieldToHenselianFraction Z (f : RationalFunction X))
  ((Ring.ord A ab.1).toNat : ℤ) - ((Ring.ord A (ab.2 : A)).toNat : ℤ)

/-- If `functionFieldToHenselianFraction` sends `f` to `IsLocalization.mk' a ⟨b, hb⟩`
with `a` and `b` nonzerodivisors, then the order is the corresponding length
difference in `O_{X, ξ}^h`. -/
theorem ord_spec (Z : PrimeDivisor X) (f : (RationalFunction X)ˣ)
    (a b : henselianLocalRing X Z.genericPoint)
    (ha : a ∈ nonZeroDivisors (henselianLocalRing X Z.genericPoint))
    (hb : b ∈ nonZeroDivisors (henselianLocalRing X Z.genericPoint))
    (hrep :
      functionFieldToHenselianFraction Z (f : RationalFunction X) =
        IsLocalization.mk'
          (FractionRing (henselianLocalRing X Z.genericPoint)) a ⟨b, hb⟩) :
    ord Z f =
      ((Ring.ord (henselianLocalRing X Z.genericPoint) a).toNat : ℤ) -
        ((Ring.ord (henselianLocalRing X Z.genericPoint) b).toNat : ℤ) :=
  sorry

end PrimeDivisor

/-- Lemma 72.6.6 (1): Let `S` be a scheme. Let `X` be a locally Noetherian
integral algebraic space over `S`. Let `f ∈ (RationalFunction X)ˣ`. Then the
collection of prime divisors `Z` with generic point `ξ` such that `f` is not in
`O_{X, ξ}` is locally finite in `X`. -/
@[stacks 0ENN]
theorem locallyFinite_primeDivisors_not_mem_henselianLocalRing {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsLocallyNoetherian X] [IsIntegral X]
    (f : (RationalFunction X)ˣ) :
    LocallyFinite fun Z : PrimeDivisor X ↦
      {x | ¬ Z.mem_henselianLocalRing (f : RationalFunction X) ∧ x ∈ Z.pointsSet} :=
  sorry

/-- Lemma 72.6.6 (2): Let `S` be a scheme. Let `X` be a locally Noetherian
integral algebraic space over `S`. Let `f ∈ (RationalFunction X)ˣ`. Then the
collection of prime divisors `Z` with `ord_Z(f) ≠ 0` is locally finite in `X`. -/
@[stacks 0ENN]
theorem locallyFinite_primeDivisors_ord_ne_zero {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsLocallyNoetherian X] [IsIntegral X]
    (f : (RationalFunction X)ˣ) :
    LocallyFinite fun Z : PrimeDivisor X ↦
      if Z.ord f = 0 then (∅ : Set (Points X)) else Z.pointsSet :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
