/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Ring.ULift
public import stacks_project.Chap71.Lemma_71_11_2_RestrictionComposition
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import Mathlib.Topology.LocallyFinite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InvertiblePullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.GenericSection
public import ReasLib.RingTheory.LocalRing.TameSymbol.TotalFractionRing
public import stacks_project.Chap67.Lemma_67_4_9
public import stacks_project.Chap71.Lemma_71_10_7
public import stacks_project.Chap72.Lemma_72_4_2_Comparison
public import stacks_project.Chap82.Definition_82_15_1_ClosedPushforward
public import stacks_project.Chap82.Definition_82_17_1_Cycle
public import stacks_project.Chap82.Remark_82_5_1_IrreducibleComponent

/-!
# Key-formula terms on algebraic spaces

This module records the one-prime contribution to the algebraic-space key
formula, together with henselian quotient units, restricted generators, and
tame symbols. It follows the Chap82 cycle owners; the Chap72 order-presentation
module is not imported because it is environment-incompatible with those
owners.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory Opposite PresheafOfModules
open Function Set Topology
open AlgebraicGeometry.AlgebraicSpace.FieldValuedPoint
open scoped nonZeroDivisors

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- The residue map of a henselian local ring of a decent algebraic space is a
local homomorphism. -/
instance instIsLocalHom_henselianLocalRingToResidueField {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsDecent X] (x : Points X) :
    IsLocalHom (henselianLocalRingToResidueField x) :=
  sorry

namespace PrimeDivisor

section
variable {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]

/-- The underlying algebraic space of a prime divisor is integral. -/
instance instIsIntegral_space (Z : PrimeDivisor X) : IsIntegral Z.space :=
  Z.isIntegral_space

/-- The underlying algebraic space of a prime divisor is decent. -/
instance instIsDecent_space (Z : PrimeDivisor X) : IsDecent Z.space :=
  ClosedSubspace.instIsDecent Z.subspace

/-- The space of points of a prime divisor is nonempty. -/
instance instNonempty_points_space (Z : PrimeDivisor X) : Nonempty (Points Z.space) :=
  sorry

/-- The generic point of a prime divisor, as a point of its underlying algebraic
space. -/
noncomputable def spaceGenericPoint (Z : PrimeDivisor X) : Points Z.space :=
  Function.invFun (Points.map Z.ι) Z.genericPoint

/-- `spaceGenericPoint Z` is a generic point of `Z.space`. -/
theorem spaceGenericPoint_mem (Z : PrimeDivisor X) :
    spaceGenericPoint Z ∈ genericPoints Z.space :=
  sorry

/-- The closed immersion of a prime divisor sends its generic point to the
ambient generic point of the support. -/
theorem spaceGenericPoint_map (Z : PrimeDivisor X) :
    Points.map Z.ι (spaceGenericPoint Z) = Z.genericPoint :=
  sorry

end

section
variable {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]

/-- Pullbacks of meromorphic sections along the residue-field point of a prime
divisor are defined: the unique point of the residue spectrum maps to the
generic point of `Z.space`. -/
instance instPullbacksMeromorphic_genericResidue (Z : PrimeDivisor X) :
    PullbacksMeromorphicFunctionsDefined
      (Z.space.fromSpecResidueField (spaceGenericPoint Z)) :=
  pullbacksMeromorphicFunctionsDefined_of_weakAss_mapsTo_codimZero _
    sorry

end

section
variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable [IsLocallyNoetherian X] [IsIntegral X]

/-- The henselian local ring at the generic point of a prime divisor has Krull
dimension one. -/
theorem ringKrullDim_henselianLocalRing (Z : PrimeDivisor X) :
    ringKrullDim (henselianLocalRing X Z.genericPoint) = 1 :=
  sorry

/-- The henselian local ring at the generic point of a prime divisor is
Noetherian. -/
instance instIsNoetherianRing_henselianLocalRing (Z : PrimeDivisor X) :
    IsNoetherianRing (henselianLocalRing X Z.genericPoint) :=
  sorry

/-- The residue field of `O_{X, ξ}^h` maps to the function field of a prime
divisor by the named henselian residue comparison, the residue-field map of
`Z.ι`, and the rational-function identification on `Z.space`. -/
noncomputable def residueToFunctionField (Z : PrimeDivisor X) :
    IsLocalRing.ResidueField (henselianLocalRing X Z.genericPoint) →+*
      RationalFunction Z.space :=
  (rationalFunctionRingEquivResidueField (spaceGenericPoint_mem Z)).symm.toRingHom.comp
    ((RingHom.ulift (Hom.residueFieldHom Z.ι (spaceGenericPoint Z)).hom).comp
      ((RingEquiv.cast (R := fun x : Points X ↦ ULift.{u + 1} (X.residueField x))
          (spaceGenericPoint_map Z).symm).toRingHom.comp
        (IsLocalRing.ResidueField.lift (henselianLocalRingToResidueField Z.genericPoint))))

/-- On residues of henselian local sections, `residueToFunctionField` agrees with
the assembled comparison of named residue and function-field maps. -/
theorem residueToFunctionField_comp_residue (Z : PrimeDivisor X)
    (a : henselianLocalRing X Z.genericPoint) :
    residueToFunctionField Z (IsLocalRing.residue _ a) =
      (rationalFunctionRingEquivResidueField (spaceGenericPoint_mem Z)).symm
        ((RingHom.ulift (Hom.residueFieldHom Z.ι (spaceGenericPoint Z)).hom)
          ((RingEquiv.cast (R := fun x : Points X ↦ ULift.{u + 1} (X.residueField x))
              (spaceGenericPoint_map Z).symm)
            (henselianLocalRingToResidueField Z.genericPoint a))) :=
  sorry

/-- The tame symbol of two henselian fraction units, transported to the function
field of the prime divisor. -/
noncomputable def tameSymbolOnSpace (Z : PrimeDivisor X)
    (f g : (FractionRing (henselianLocalRing X Z.genericPoint))ˣ) :
    (RationalFunction Z.space)ˣ :=
  Units.map (residueToFunctionField Z).toMonoidHom
    (TameSymbol.Total.value (henselianLocalRing X Z.genericPoint)
      (FractionRing (henselianLocalRing X Z.genericPoint))
      (ringKrullDim_henselianLocalRing Z) f g)

/-- The space-level tame symbol is the image of the total tame symbol under the
canonical residue-to-function-field map. -/
theorem tameSymbolOnSpace_def (Z : PrimeDivisor X)
    (f g : (FractionRing (henselianLocalRing X Z.genericPoint))ˣ) :
    tameSymbolOnSpace Z f g =
      Units.map (residueToFunctionField Z).toMonoidHom
        (TameSymbol.Total.value (henselianLocalRing X Z.genericPoint)
          (FractionRing (henselianLocalRing X Z.genericPoint))
          (ringKrullDim_henselianLocalRing Z) f g) :=
  sorry

/-- The ratio of two nonzerodivisors in the henselian local ring, as a unit of
the total fraction ring. -/
noncomputable def quotientUnits (Z : PrimeDivisor X)
    (num den : henselianLocalRing X Z.genericPoint)
    (hnum : num ∈ nonZeroDivisors (henselianLocalRing X Z.genericPoint))
    (hden : den ∈ nonZeroDivisors (henselianLocalRing X Z.genericPoint)) :
    (FractionRing (henselianLocalRing X Z.genericPoint))ˣ where
  val := Localization.mk num ⟨den, hden⟩
  inv := Localization.mk den ⟨num, hnum⟩
  val_inv := sorry
  inv_val := sorry

/-- The underlying fraction of `quotientUnits` is the localization class of the
numerator and denominator. -/
theorem quotientUnits_val (Z : PrimeDivisor X)
    (num den : henselianLocalRing X Z.genericPoint)
    (hnum : num ∈ nonZeroDivisors (henselianLocalRing X Z.genericPoint))
    (hden : den ∈ nonZeroDivisors (henselianLocalRing X Z.genericPoint)) :
    (quotientUnits Z num den hnum hden :
        FractionRing (henselianLocalRing X Z.genericPoint)) =
      Localization.mk num ⟨den, hden⟩ :=
  sorry

/-- The order of a henselian fraction unit, as the length difference of a
numerator-denominator presentation. -/
noncomputable def fractionUnitOrder (Z : PrimeDivisor X)
    (u : (FractionRing (henselianLocalRing X Z.genericPoint))ˣ) : ℤ :=
  let A := henselianLocalRing X Z.genericPoint
  let ab := IsLocalization.sec (nonZeroDivisors A) (u : FractionRing A)
  ((Ring.ord A ab.1).toNat : ℤ) - ((Ring.ord A (ab.2 : A)).toNat : ℤ)

/-- The order of a henselian fraction unit is the length difference of its
canonical numerator and denominator. -/
theorem fractionUnitOrder_eq (Z : PrimeDivisor X)
    (u : (FractionRing (henselianLocalRing X Z.genericPoint))ˣ) :
    fractionUnitOrder Z u =
      let A := henselianLocalRing X Z.genericPoint
      let ab := IsLocalization.sec (nonZeroDivisors A) (u : FractionRing A)
      ((Ring.ord A ab.1).toNat : ℤ) - ((Ring.ord A (ab.2 : A)).toNat : ℤ) :=
  sorry

end

end PrimeDivisor

namespace MeromorphicSection

variable {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]

/-- The ratio `s / s_ξ` as a unit of `Q(O_{X,ξ}^h)`, whose underlying value is
`henselianFraction s hs Z`. -/
noncomputable def henselianFractionUnit {L : X.Modules} [isInvertibleObject L]
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s)
    (Z : PrimeDivisor X) :
    (FractionRing (henselianLocalRing X Z.genericPoint))ˣ where
  val := henselianFraction s hs Z
  inv := Ring.inverse (henselianFraction s hs Z)
  val_inv := sorry
  inv_val := sorry

/-- The underlying fraction of `henselianFractionUnit` is `henselianFraction`. -/
theorem henselianFractionUnit_val {L : X.Modules} [isInvertibleObject L]
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s)
    (Z : PrimeDivisor X) :
    (henselianFractionUnit s hs Z :
        FractionRing (henselianLocalRing X Z.genericPoint)) =
      henselianFraction s hs Z :=
  sorry

/-- The unit `henselianFractionUnit s hs Z` presents the pulled germ of `s`. -/
theorem henselianFractionUnit_spec {L : X.Modules} [isInvertibleObject L]
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s)
    (Z : PrimeDivisor X) :
    IsRatioOfPulledGerm s Z (henselianFractionUnit s hs Z :
        FractionRing (henselianLocalRing X Z.genericPoint)) :=
  sorry

end MeromorphicSection

/-- The generic germ of a meromorphic section of `L|_Z` at the residue-field
point of `spaceGenericPoint Z`. -/
noncomputable def genericGerm {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    (Z : PrimeDivisor X) {L : X.Modules}
    (sZ : meromorphicSections Z.space ((Modules.pullback Z.ι).obj L)) :
    MeromorphicConstruction.GenericSection.fibre
      (FieldValuedPoint.residuePoint (PrimeDivisor.spaceGenericPoint Z))
      ((Modules.pullback Z.ι).obj L) :=
  MeromorphicConstruction.GenericSection.alongPoint
    (FieldValuedPoint.residuePoint (PrimeDivisor.spaceGenericPoint Z))
    ((Modules.pullback Z.ι).obj L) sZ

/-- The generic germ of `sZ` is evaluation of its pullback along the residue-field
point of `Z`. -/
theorem genericGerm_eq {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    (Z : PrimeDivisor X) {L : X.Modules}
    (sZ : meromorphicSections Z.space ((Modules.pullback Z.ι).obj L)) :
    genericGerm Z sZ =
      MeromorphicConstruction.GenericSection.alongPoint
        (FieldValuedPoint.residuePoint (PrimeDivisor.spaceGenericPoint Z))
        ((Modules.pullback Z.ι).obj L) sZ :=
  sorry

/-- A regular meromorphic section generates the henselian fibre at a prime
divisor when the pulled ratio may be taken to be `1`. -/
def GeneratesHenselianFibre {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] {L : X.Modules} [isInvertibleObject L]
    (s : meromorphicSections X L) (Z : PrimeDivisor X) : Prop :=
  MeromorphicSection.IsRatioOfPulledGerm s Z
    (1 : FractionRing (henselianLocalRing X Z.genericPoint))

/-- Generating the henselian fibre means the pulled ratio of `s` is `1`. -/
theorem GeneratesHenselianFibre_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] {L : X.Modules} [isInvertibleObject L]
    (s : meromorphicSections X L) (Z : PrimeDivisor X) :
    GeneratesHenselianFibre s Z ↔
      MeromorphicSection.IsRatioOfPulledGerm s Z
        (1 : FractionRing (henselianLocalRing X Z.genericPoint)) :=
  sorry

namespace KeyFormulaPresentation

variable {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]

abbrev henselianModule (L : X.Modules) (Z : PrimeDivisor X) :=
  (Modules.pullback (fromHenselization X Z.genericPoint)).obj L

abbrev identityChart (Z : PrimeDivisor X) :=
  op (smallEtaleSite.id (henselizationOver X Z.genericPoint))

abbrev identityRing (Z : PrimeDivisor X) :=
  (commStructureSheafLift (henselizationSpace X Z.genericPoint)).obj.obj (identityChart Z)

abbrev residuePoint (Z : PrimeDivisor X) :=
  FieldValuedPoint.residuePoint (PrimeDivisor.spaceGenericPoint Z)

/-- The named residue map, with the prime-divisor residue-field comparison. -/
def residueCoefficient (Z : PrimeDivisor X) :
    henselianLocalRing X Z.genericPoint →+* ULift.{u + 1} (residuePoint Z).K :=
  (RingHom.ulift (Hom.residueFieldHom Z.ι (PrimeDivisor.spaceGenericPoint Z)).hom).comp
    ((RingEquiv.cast (R := fun x : Points X ↦ ULift.{u + 1} (X.residueField x))
      (PrimeDivisor.spaceGenericPoint_map Z).symm).toRingHom.comp
        (henselianLocalRingToResidueField Z.genericPoint))

/-- Use this same ring identification for the fraction and its residue. -/
def residueOnSections (Z : PrimeDivisor X)
    (e : henselianLocalRing X Z.genericPoint ≃+* identityRing Z) :
    Γ((henselizationOver X Z.genericPoint).left, ⊤) →+* (residuePoint Z).K :=
  ULift.ringEquiv.toRingHom.comp
    ((residueCoefficient Z).comp (e.symm.toRingHom.comp ULift.ringEquiv.symm.toRingHom))

/-- Actual Spec of that coefficient map, followed by the affine identification. -/
def residueSchemeMap (Z : PrimeDivisor X)
    (e : henselianLocalRing X Z.genericPoint ≃+* identityRing Z) :
    (residuePoint Z).overObj.left ⟶ (henselizationOver X Z.genericPoint).left := by
  -- Local instance justification (defeq pin): This displayed henselization is Spec of its actual ring, so its affine identification is the canonical Spec identification used by the residue map.
  letI : IsAffine (henselizationOver X Z.genericPoint).left :=
    inferInstanceAs (IsAffine (Spec (.of (henselizationRing X Z.genericPoint))))
  exact Spec.map (CommRingCat.ofHom (residueOnSections Z e)) ≫
    (henselizationOver X Z.genericPoint).left.isoSpec.inv

/-- The top open of a represented scheme maps to its identity étale chart. -/
def topToIdentity (H : Over S) :
    Modules.RestrictToScheme.siteObject H ⊤ ⟶ smallEtaleSite.id H :=
  MorphismProperty.CostructuredArrow.homMk
    (Over.homMk (Scheme.topIso H.left).hom sorry) trivial sorry

/-- Read the specified identity-chart module value as the corresponding section. -/
def identitySection (H : Over S) (M : (ofOver H).Modules)
    (t : (Modules.liftModule M).val.obj (op (smallEtaleSite.id H))) :
    Γ((Modules.restrictToScheme H).obj M, ⊤) :=
  (Modules.RestrictToScheme.sectionEquiv H M ⊤).symm
    (M.val.map (topToIdentity H).op t.down)

/-- One source local presentation. The geometric triangles constrain the same
coordinate identification used in its ratio; no second ring equivalence occurs. -/
structure LocalPresentation {L : X.Modules} [isInvertibleObject L]
    (s : meromorphicSections X L) (Z : PrimeDivisor X) where
  /-- The same henselian coordinates are used for both the fraction and residue. -/
  ringEquiv : henselianLocalRing X Z.genericPoint ≃+* identityRing Z
  /-- The source's chosen generator of the pulled-back invertible module. -/
  generator : (Modules.liftModule (henselianModule L Z)).val.obj (identityChart Z)
  /-- The actual generator spans the rank-one module over its local ring. -/
  generator_span : Submodule.span (identityRing Z) {generator} = ⊤
  /-- Numerator of the section's ratio relative to this generator. -/
  numerator : henselianLocalRing X Z.genericPoint
  /-- Denominator of that same ratio. -/
  denominator : henselianLocalRing X Z.genericPoint
  /-- Regularity makes the numerator a nonzerodivisor. -/
  numerator_regular : numerator ∈ nonZeroDivisors (henselianLocalRing X Z.genericPoint)
  /-- The fraction denominator is a nonzerodivisor. -/
  denominator_regular : denominator ∈ nonZeroDivisors (henselianLocalRing X Z.genericPoint)
  /-- Its image is an allowed denominator in the actual meromorphic presheaf. -/
  denominator_section_regular : ringEquiv denominator ∈
    (regularStructureSections (henselizationSpace X Z.genericPoint)).obj (identityChart Z)
  /-- The ratio times this generator is the actual pulled germ of s. -/
  germ_eq :
    (CategoryTheory.toSheafify (smallEtaleTopology (henselizationSpace X Z.genericPoint))
      (meromorphicSectionPresheaf (henselizationSpace X Z.genericPoint)
        (henselianModule L Z)).presheaf).app (identityChart Z)
      (LocalizedModule.mk (ringEquiv numerator • generator)
        ⟨ringEquiv denominator, denominator_section_regular⟩) =
      sections.eval (pullbackMeromorphicSections (fromHenselization X Z.genericPoint) L s)
        (identityChart Z)
  /-- The induced Spec residue map has the original base structure. -/
  residue_over_base : residueSchemeMap Z ringEquiv ≫
    (henselizationOver X Z.genericPoint).hom = (residuePoint Z).overObj.hom
  /-- It is the residue point over X, not a second unrelated coordinate choice. -/
  residue_over_X :
    ofOverMap (Over.homMk (residueSchemeMap Z ringEquiv) residue_over_base) ≫
      fromHenselization X Z.genericPoint = (residuePoint Z).hom ≫ Z.ι

namespace LocalPresentation
variable {L : X.Modules} [isInvertibleObject L]
    {s : meromorphicSections X L} {Z : PrimeDivisor X}

/-- The actual ratio of this presentation's regular numerator and denominator. -/
def fraction (d : LocalPresentation s Z) :
    (FractionRing (henselianLocalRing X Z.genericPoint))ˣ :=
  { val := IsLocalization.mk' _ d.numerator ⟨d.denominator, d.denominator_regular⟩
    inv := IsLocalization.mk' _ d.denominator ⟨d.numerator, d.numerator_regular⟩
    val_inv := sorry
    inv_val := sorry }

/-- The concrete ratio and the residue image use this very same generator
and ring identification, now exposed from the source local presentation. -/
theorem fraction_isRatio (d : LocalPresentation s Z) :
    MeromorphicSection.IsRatioOfPulledGerm s Z (d.fraction :
      FractionRing (henselianLocalRing X Z.genericPoint)) := by
  refine ⟨d.generator, d.numerator, d.denominator, d.denominator_regular,
    d.ringEquiv, d.denominator_section_regular, d.numerator_regular,
    d.generator_span, ?_, d.germ_eq⟩
  rfl

/-- The same residue morphism regarded over the original base. -/
def residueOver (d : LocalPresentation s Z) :
    (residuePoint Z).overObj ⟶ henselizationOver X Z.genericPoint :=
  Over.homMk (residueSchemeMap Z d.ringEquiv) d.residue_over_base

/-- Common carrier: the original module pulled back to the specified residue point. -/
abbrev fibreSections (L : X.Modules) (Z : PrimeDivisor X) : Type u :=
  Γ((Modules.restrictToScheme (residuePoint Z).overObj).obj
    ((Modules.pullback ((residuePoint Z).hom ≫ Z.ι)).obj L), ⊤)

/-- Pull the same generator along its actual Spec residue map, then the
canonical composition comparison and its actual commuting triangle. -/
def generatorImage (d : LocalPresentation s Z) : fibreSections L Z :=
  let value := (Scheme.Modules.globalSectionsMap
      (Modules.RestrictToScheme.compositePullbackComparison
        (fromHenselization X Z.genericPoint) d.residueOver L)).hom
    ((Scheme.Modules.globalSectionsPullback d.residueOver.left
      ((Modules.restrictToScheme (henselizationOver X Z.genericPoint)).obj
        (henselianModule L Z))).hom
      (identitySection (henselizationOver X Z.genericPoint) (henselianModule L Z) d.generator))
  cast (congrArg (fun h ↦ (Γ((Modules.restrictToScheme (residuePoint Z).overObj).obj
    ((Modules.pullback h).obj L), ⊤) : Type u)) d.residue_over_X) value

/-- Evaluate a meromorphic section of L|Z at the actual generic residue point,
then compose the two specified module pullbacks. -/
def genericRestriction (sZ : meromorphicSections Z.space ((Modules.pullback Z.ι).obj L)) :
    fibreSections L Z :=
  identitySection (residuePoint Z).overObj
    ((Modules.pullback ((residuePoint Z).hom ≫ Z.ι)).obj L)
    (ULift.up ((((Modules.pullbackCompIso (residuePoint Z).hom Z.ι).hom.app L).val.app
      (op (smallEtaleSite.id (residuePoint Z).overObj))) (genericGerm Z sZ)))

/-- On an integral decent space, meromorphic sections of an invertible module
are its ordinary generic fibre. The first map here is exactly that evaluation;
restriction at the represented top open and the pullback-composition map are
isomorphisms. Thus this specified composite is bijective. -/
theorem genericRestriction_bijective :
    Function.Bijective (genericRestriction (L := L) (Z := Z)) := sorry

/-- Invert only the displayed generic restriction, with its fixed-map law. -/
def genericRestrictionEquiv :
    meromorphicSections Z.space ((Modules.pullback Z.ι).obj L) ≃ fibreSections L Z :=
  Equiv.ofBijective genericRestriction genericRestriction_bijective

/-- Recover precisely the generator's residue image by inverting that fixed map. -/
def restrictedSection (d : LocalPresentation s Z) :
    meromorphicSections Z.space ((Modules.pullback Z.ι).obj L) :=
  genericRestrictionEquiv.symm d.generatorImage

theorem restrictedSection_generic (d : LocalPresentation s Z) :
    genericRestriction d.restrictedSection = d.generatorImage :=
  genericRestrictionEquiv.apply_symm_apply d.generatorImage

/-- The image of a spanning henselian generator at its residue point is
nonzero, so the resulting meromorphic section of the invertible line is regular. -/
theorem restrictedSection_regular (d : LocalPresentation s Z) :
    IsRegularMeromorphicSection Z.space ((Modules.pullback Z.ι).obj L) d.restrictedSection :=
  sorry

end LocalPresentation
end KeyFormulaPresentation

namespace Hom

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]

variable [IsIntegral X]

/-- The restriction of a good structure morphism to a prime divisor remains
quasi-separated. -/
instance instQuasiSeparated_primeDivisor_structure (Z : PrimeDivisor X) :
    QuasiSeparated (Z.ι ≫ f) :=
  sorry

/-- The restriction of a good structure morphism to a prime divisor remains
locally of finite type. -/
instance instLocallyOfFiniteType_primeDivisor_structure (Z : PrimeDivisor X) :
    LocallyOfFiniteType (Z.ι ≫ f) :=
  sorry

/-- Pullback of an invertible module along a prime-divisor immersion remains
invertible. -/
instance instIsInvertibleObject_pullback_primeDivisor (Z : PrimeDivisor X)
    (L : X.Modules) [isInvertibleObject L] :
    isInvertibleObject ((Modules.pullback Z.ι).obj L) :=
  Modules.isInvertibleObject_pullback Z.ι L

/-- Restrict the generator from the same local ratio presentation. -/
noncomputable def restrictToPrimeDivisor (Z : PrimeDivisor X)
    {L : X.Modules} [isInvertibleObject L] {s : meromorphicSections X L}
    (d : KeyFormulaPresentation.LocalPresentation s Z) :
    meromorphicSections Z.space ((Modules.pullback Z.ι).obj L) :=
  d.restrictedSection

/-- In the common generic-fibre carrier, the restricted section is precisely
that presentation generator's image along its residue map. -/
theorem restrictToPrimeDivisor_genericGerm (Z : PrimeDivisor X)
    {L : X.Modules} [isInvertibleObject L] {s : meromorphicSections X L}
    (d : KeyFormulaPresentation.LocalPresentation s Z) :
    KeyFormulaPresentation.LocalPresentation.genericRestriction
      (restrictToPrimeDivisor Z d) = d.generatorImage :=
  d.restrictedSection_generic

/-- This specified restricted generator is a regular meromorphic section. -/
theorem restrictToPrimeDivisor_isRegular (Z : PrimeDivisor X)
    {L : X.Modules} [isInvertibleObject L] {s : meromorphicSections X L}
    (d : KeyFormulaPresentation.LocalPresentation s Z) :
    IsRegularMeromorphicSection Z.space ((Modules.pullback Z.ι).obj L)
      (restrictToPrimeDivisor Z d) :=
  d.restrictedSection_regular

/-- A regular meromorphic section of an invertible module admits the source's
local trivialization and fraction at a prime divisor. The coordinate choice
uses the actual henselian identification and its canonical residue triangle.
This range certificate is not used to select any section or formula data. -/
theorem localPresentation_nonempty (Z : PrimeDivisor X)
    {L : X.Modules} [isInvertibleObject L]
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s) :
    Nonempty (KeyFormulaPresentation.LocalPresentation s Z) :=
  sorry

variable (δ : Points B → ℤ) [IsDimensionFunction δ]

variable (n : ℤ) (hX : deltaDimension f δ (univIrreducibleClosed X) = n)

include hX in
/-- The support of a prime divisor has `δ`-dimension `(n - 2) + 1` when
`dim_δ(X) = n`. -/
theorem primeDivisor_deltaDimension (Z : PrimeDivisor X) :
    deltaDimension f δ (ClosedSubspace.irreducibleClosed Z.subspace) =
      n - 2 + 1 :=
  sorry

variable (L N : X.Modules) [isInvertibleObject L] [isInvertibleObject N]

/-- The contribution of one prime divisor to the key formula: the order of the
henselian ratio of `s` times the pushed-forward divisor of the restricted
generator of `t`, minus the symmetric term. -/
noncomputable def keyFormulaTerm (Z : PrimeDivisor X)
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s)
    (t : meromorphicSections X N) (ht : IsRegularMeromorphicSection X N t)
    (sData : KeyFormulaPresentation.LocalPresentation s Z)
    (tData : KeyFormulaPresentation.LocalPresentation t Z) :
    Function.locallyFinsupp (Points X) ℤ :=
  let _ := n
  let _ := hX
  closedImmersionPushforwardCycle Z.subspace
    (PrimeDivisor.fractionUnitOrder Z sData.fraction •
        meromorphicSectionDivisorCycle (Z.ι ≫ f) δ (restrictToPrimeDivisor Z tData)
          (restrictToPrimeDivisor_isRegular Z tData) -
      PrimeDivisor.fractionUnitOrder Z tData.fraction •
        meromorphicSectionDivisorCycle (Z.ι ≫ f) δ (restrictToPrimeDivisor Z sData)
          (restrictToPrimeDivisor_isRegular Z sData))

/-- Unfolding a key-formula contribution displays its two order-weighted
pushed-forward divisor cycles. -/
theorem keyFormulaTerm_def (Z : PrimeDivisor X)
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s)
    (t : meromorphicSections X N) (ht : IsRegularMeromorphicSection X N t)
    (sData : KeyFormulaPresentation.LocalPresentation s Z)
    (tData : KeyFormulaPresentation.LocalPresentation t Z) :
    keyFormulaTerm f δ n hX L N Z s hs t ht sData tData =
      closedImmersionPushforwardCycle Z.subspace
        (PrimeDivisor.fractionUnitOrder Z
            sData.fraction •
            meromorphicSectionDivisorCycle (Z.ι ≫ f) δ (restrictToPrimeDivisor Z tData)
              (restrictToPrimeDivisor_isRegular Z tData) -
          PrimeDivisor.fractionUnitOrder Z
            tData.fraction •
            meromorphicSectionDivisorCycle (Z.ι ≫ f) δ (restrictToPrimeDivisor Z sData)
              (restrictToPrimeDivisor_isRegular Z sData)) :=
  sorry

/-- A one-prime key-formula contribution is an `(n-2)`-cycle. -/
theorem keyFormulaTerm_mem_cycleGroup (Z : PrimeDivisor X)
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s)
    (t : meromorphicSections X N) (ht : IsRegularMeromorphicSection X N t)
    (sData : KeyFormulaPresentation.LocalPresentation s Z)
    (tData : KeyFormulaPresentation.LocalPresentation t Z) :
    keyFormulaTerm f δ n hX L N Z s hs t ht sData tData ∈
      cycleGroup f δ (n - 2) :=
  sorry

/-- The supports of the component terms in the key formula are locally finite
when the chosen prime divisors are locally finite. -/
theorem keyFormulaTermsLocallyFinite {I : Type v} (Z : I → PrimeDivisor X)
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s)
    (t : meromorphicSections X N) (ht : IsRegularMeromorphicSection X N t)
    (hlocal : LocallyFinite fun i ↦ ((Z i).pointsSet : Set (Points X)))
    (sData : ∀ i, KeyFormulaPresentation.LocalPresentation s (Z i))
    (tData : ∀ i, KeyFormulaPresentation.LocalPresentation t (Z i)) :
    LocallyFinite fun i ↦
      (keyFormulaTerm f δ n hX L N (Z i) s hs t ht (sData i) (tData i)).support :=
  sorry


/-- The tame symbol on a prime divisor, using local Noetherianity of a good
structure morphism. -/
noncomputable def tameSymbolOnSpace_ofGood (Z : PrimeDivisor X)
    (fi gi : (FractionRing (henselianLocalRing X Z.genericPoint))ˣ) :
    (RationalFunction Z.space)ˣ :=
  @PrimeDivisor.tameSymbolOnSpace S X
    (LocallyOfFiniteType.isLocallyNoetherian f) inferInstance Z fi gi

/-- The good-structure tame symbol is the prime-divisor tame symbol. -/
theorem tameSymbolOnSpace_ofGood_eq (Z : PrimeDivisor X)
    (fi gi : (FractionRing (henselianLocalRing X Z.genericPoint))ˣ) :
    tameSymbolOnSpace_ofGood f Z fi gi =
      @PrimeDivisor.tameSymbolOnSpace S X
        (LocallyOfFiniteType.isLocallyNoetherian f) inferInstance Z fi gi :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
