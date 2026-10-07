module

public import Mathlib.RingTheory.Localization.FractionRing
public import ReasLib.RingTheory.Localization.TotalQuotient
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_47_3_RationalFunction
public import stacks_project.Chap68.Definition_68_11_7_HenselianLocalRing
public import stacks_project.Chap72.Definition_72_6_2_Prime

/-!
# Function-field comparison into henselian total quotients

Pullback of rational functions along dense-open-preserving morphisms, the
comparison from total quotients of global sections to rational functions, and
the coprojection of `henselianLocalRing.ι` on nonzerodivisors.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry nonZeroDivisors

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- A morphism of algebraic spaces preserves dense opens when the pullback of every
dense open subspace remains dense. -/
def PreservesDenseOpens {X Y : AlgebraicSpace S} (f : Y ⟶ X) : Prop :=
  ∀ U : smallZariskiSite X, IsDense U.hom → IsDense (domainInfFst f U.hom)

/-- Preservation of dense opens is the pullback-density condition on Zariski opens. -/
theorem preservesDenseOpens_iff {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    PreservesDenseOpens f ↔
      ∀ U : smallZariskiSite X, IsDense U.hom → IsDense (domainInfFst f U.hom) :=
  sorry

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

/-- The underlying morphism of a pulled-back partial map is the second projection
followed by the original morphism. -/
theorem PartialMap.precomp_hom {X Y Z : AlgebraicSpace S} (φ : PartialMap X Z)
    {f : Y ⟶ X} (hf : PreservesDenseOpens f) :
    (φ.precomp hf).hom = domainInfSnd f φ.domain.hom ≫ φ.hom :=
  sorry

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
      (fun _ _ h ↦ PartialMap.precomp_toRationalMap_respects hf h)
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- Pullback of rational functions on a partial-map representative is precomposition. -/
theorem rationalFunctionComap_toRationalMap {X Y : AlgebraicSpace S} {f : Y ⟶ X}
    (hf : PreservesDenseOpens f) (φ : PartialMap X (affineLine S)) :
    rationalFunctionComap hf φ.toRationalMap = (φ.precomp hf).toRationalMap :=
  sorry

/-- Global sections of a scheme over `S`, viewed as rational functions on the
associated algebraic space. -/
def sectionsToRationalFunction (T : Over S) :
    Γ(T.left, ⊤) →+* RationalFunction (ofOver T) where
  toFun s := (PartialMap.ofHom (ofOverMap (homOfCoord T s))).toRationalMap
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- The image of a global section as a rational function is the morphism classified
by that section. -/
theorem sectionsToRationalFunction_apply (T : Over S) (s : Γ(T.left, ⊤)) :
    sectionsToRationalFunction T s =
      (PartialMap.ofHom (ofOverMap (homOfCoord T s))).toRationalMap :=
  sorry

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

/-- The comparison from total quotients of global sections extends the map on
sections. -/
theorem sectionsFractionsToRationalFunction_algebraMap (T : Over S)
    (s : Γ(T.left, ⊤)) :
    sectionsFractionsToRationalFunction T (algebraMap _ _ s) =
      sectionsToRationalFunction T s :=
  sorry

/-- The colimit coprojection `henselianLocalRing.ι` sends nonzerodivisors to
nonzerodivisors. -/
theorem henselianLocalRing.ι_maps_nonZeroDivisors {X : AlgebraicSpace S} [IsDecent X]
    {x : Points X} (U : EtaleNeighborhood.Elementary X x) :
    nonZeroDivisors Γ((EtaleNeighborhood.Elementary.toScheme X x).obj U, ⊤) ≤
      Submonoid.comap (henselianLocalRing.ι X x U)
        (nonZeroDivisors (henselianLocalRing X x)) :=
  sorry

/-- The identification of `R(U)` with `Q(Γ(U, ⊤))` on an elementary neighbourhood
where the comparison is bijective, using the same global-section carrier as
`henselianLocalRing.ι`. -/
def neighbourhoodFractionsEquiv {X : AlgebraicSpace S} {ξ : Points X}
    (U : EtaleNeighborhood.Elementary X ξ)
    (hU : Function.Bijective (sectionsFractionsToRationalFunction U.obj.toOver)) :
    FractionRing Γ((EtaleNeighborhood.Elementary.toScheme X ξ).obj U, ⊤) ≃+*
      RationalFunction (ofOver U.obj.toOver) :=
  RingEquiv.ofBijective (sectionsFractionsToRationalFunction U.obj.toOver) hU

/-- The equivalence `neighbourhoodFractionsEquiv` is the sections-to-rational-functions
comparison. -/
theorem neighbourhoodFractionsEquiv_apply {X : AlgebraicSpace S} {ξ : Points X}
    (U : EtaleNeighborhood.Elementary X ξ)
    (hU : Function.Bijective (sectionsFractionsToRationalFunction U.obj.toOver))
    (s : FractionRing Γ((EtaleNeighborhood.Elementary.toScheme X ξ).obj U, ⊤)) :
    neighbourhoodFractionsEquiv U hU s =
      sectionsFractionsToRationalFunction U.obj.toOver s :=
  sorry

section PrimeDivisorComparison

variable {X : AlgebraicSpace S}
variable [h_locallyNoetherian : IsLocallyNoetherian X] [h_integral : IsIntegral X]

include h_locallyNoetherian h_integral

/-- There is an elementary étale neighbourhood of the generic point of a prime
divisor on which the comparison from the total quotient ring of global sections
to rational functions is bijective. -/
theorem exists_elementary_sectionsFractions_bijective (Z : PrimeDivisor X) :
    ∃ U : EtaleNeighborhood.Elementary X Z.genericPoint,
      Function.Bijective (sectionsFractionsToRationalFunction U.obj.toOver) :=
  sorry

end PrimeDivisorComparison

end AlgebraicGeometry.AlgebraicSpace
