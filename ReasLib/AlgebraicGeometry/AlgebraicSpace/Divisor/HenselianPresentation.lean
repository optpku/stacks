/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Ring.ULift
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme.ExtensionComposition
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InvertiblePullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.GenericSection
public import ReasLib.RingTheory.LocalRing.TameSymbol.TotalFractionRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Transfer
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.MeromorphicFunction.Pullback.Criteria
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalFunction.GenericPoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.GenericPoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Separation

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResidueField.Morphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.HenselianLocalRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.Henselian

/-! # Henselian presentations of meromorphic sections along prime divisors -/

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

/-- The residue field of `O_{X, ξ}^h` maps to the function field of a prime
divisor by the named henselian residue comparison, the residue-field map of
`Z.ι`, and the rational-function identification on `Z.space`. -/
noncomputable def residueToFunctionField (Z : PrimeDivisor X) :
    IsLocalRing.ResidueField (henselianLocalRing X Z.genericPoint) →+*
      RationalFunction Z.space :=
  (rationalFunctionRingEquivResidueField (spaceGenericPoint_mem Z)).symm.toRingHom.comp
    ((RingHom.ulift (Hom.residueFieldMap Z.ι (spaceGenericPoint Z)).hom).comp
      ((RingEquiv.cast (R := fun x : Points X ↦ ULift.{u + 1} (X.residueField x))
          (spaceGenericPoint_map Z).symm).toRingHom.comp
        (IsLocalRing.ResidueField.lift (henselianLocalRingToResidueField Z.genericPoint))))

/-- On residues of henselian local sections, `residueToFunctionField` agrees with
the assembled comparison of named residue and function-field maps. -/
theorem residueToFunctionField_comp_residue (Z : PrimeDivisor X)
    (a : henselianLocalRing X Z.genericPoint) :
    residueToFunctionField Z (IsLocalRing.residue _ a) =
      (rationalFunctionRingEquivResidueField (spaceGenericPoint_mem Z)).symm
        ((RingHom.ulift (Hom.residueFieldMap Z.ι (spaceGenericPoint Z)).hom)
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
      (ringKrullDim_henselianLocalRing_genericPoint Z) f g)

/-- The space-level tame symbol is the image of the total tame symbol under the
canonical residue-to-function-field map. -/
theorem tameSymbolOnSpace_def (Z : PrimeDivisor X)
    (f g : (FractionRing (henselianLocalRing X Z.genericPoint))ˣ) :
    tameSymbolOnSpace Z f g =
      Units.map (residueToFunctionField Z).toMonoidHom
        (TameSymbol.Total.value (henselianLocalRing X Z.genericPoint)
          (FractionRing (henselianLocalRing X Z.genericPoint))
          (ringKrullDim_henselianLocalRing_genericPoint Z) f g) :=
  sorry

private theorem quotientUnits_laws (Z : PrimeDivisor X)
    (num den : henselianLocalRing X Z.genericPoint)
    (hnum : num ∈ nonZeroDivisors (henselianLocalRing X Z.genericPoint))
    (hden : den ∈ nonZeroDivisors (henselianLocalRing X Z.genericPoint)) :
    (Localization.mk num ⟨den, hden⟩ : FractionRing (henselianLocalRing X Z.genericPoint)) *
        Localization.mk den ⟨num, hnum⟩ = 1 ∧
      (Localization.mk den ⟨num, hnum⟩ : FractionRing (henselianLocalRing X Z.genericPoint)) *
        Localization.mk num ⟨den, hden⟩ = 1 := sorry

/-- The ratio of two nonzerodivisors in the henselian local ring, as a unit of
the total fraction ring. -/
@[no_expose] noncomputable def quotientUnits (Z : PrimeDivisor X)
    (num den : henselianLocalRing X Z.genericPoint)
    (hnum : num ∈ nonZeroDivisors (henselianLocalRing X Z.genericPoint))
    (hden : den ∈ nonZeroDivisors (henselianLocalRing X Z.genericPoint)) :
    (FractionRing (henselianLocalRing X Z.genericPoint))ˣ where
  val := Localization.mk num ⟨den, hden⟩
  inv := Localization.mk den ⟨num, hnum⟩
  val_inv := (quotientUnits_laws Z num den hnum hden).1
  inv_val := (quotientUnits_laws Z num den hnum hden).2

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

private theorem henselianFractionUnit_laws {L : X.Modules} [isInvertibleObject L]
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s)
    (Z : PrimeDivisor X) :
    henselianFraction s hs Z * Ring.inverse (henselianFraction s hs Z) = 1 ∧
      Ring.inverse (henselianFraction s hs Z) * henselianFraction s hs Z = 1 := sorry

/-- The ratio `s / s_ξ` as a unit of `Q(O_{X,ξ}^h)`, whose underlying value is
`henselianFraction s hs Z`. -/
@[no_expose] noncomputable def henselianFractionUnit {L : X.Modules} [isInvertibleObject L]
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s)
    (Z : PrimeDivisor X) :
    (FractionRing (henselianLocalRing X Z.genericPoint))ˣ where
  val := henselianFraction s hs Z
  inv := Ring.inverse (henselianFraction s hs Z)
  val_inv := (henselianFractionUnit_laws s hs Z).1
  inv_val := (henselianFractionUnit_laws s hs Z).2

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

/-- The module pulled back to a supplied henselization. -/
abbrev henselianModule (L : X.Modules) (Z : PrimeDivisor X)
    (N : EtaleNeighborhood X Z.genericPoint)
    (hN : IsAffine N.scheme ∧ Points.mapOfOver N.hom ⁻¹' {Z.genericPoint} = {N.point} ∧ N.IsElementary)
    (R : Type u) [CommRing R] [Algebra (N.scheme.presheaf.stalk N.point) R]
    [IsHenselizationOf (N.scheme.presheaf.stalk N.point) R] :=
  (Modules.pullback (fromHenselization X Z.genericPoint N hN R)).obj L

/-- The identity étale chart of a supplied henselization. -/
abbrev identityChart (Z : PrimeDivisor X)
    (N : EtaleNeighborhood X Z.genericPoint)
    (hN : IsAffine N.scheme ∧ Points.mapOfOver N.hom ⁻¹' {Z.genericPoint} = {N.point} ∧ N.IsElementary)
    (R : Type u) [CommRing R] [Algebra (N.scheme.presheaf.stalk N.point) R]
    [IsHenselizationOf (N.scheme.presheaf.stalk N.point) R] :=
  op (smallEtaleSite.id (henselizationOver X Z.genericPoint N hN R))

/-- The structure sections on the identity chart of a supplied henselization. -/
abbrev identityRing (Z : PrimeDivisor X)
    (N : EtaleNeighborhood X Z.genericPoint)
    (hN : IsAffine N.scheme ∧ Points.mapOfOver N.hom ⁻¹' {Z.genericPoint} = {N.point} ∧ N.IsElementary)
    (R : Type u) [CommRing R] [Algebra (N.scheme.presheaf.stalk N.point) R]
    [IsHenselizationOf (N.scheme.presheaf.stalk N.point) R] :=
  (commStructureSheafLift (henselizationSpace X Z.genericPoint N hN R)).obj.obj (identityChart Z N hN R)

/-- The residue-field point at the generic point of the prime divisor. -/
abbrev residuePoint (Z : PrimeDivisor X) :=
  FieldValuedPoint.residuePoint (PrimeDivisor.spaceGenericPoint Z)

/-- The named residue map, with the prime-divisor residue-field comparison. -/
def residueCoefficient (Z : PrimeDivisor X) :
    henselianLocalRing X Z.genericPoint →+* ULift.{u + 1} (residuePoint Z).K :=
  (RingHom.ulift (Hom.residueFieldMap Z.ι (PrimeDivisor.spaceGenericPoint Z)).hom).comp
    ((RingEquiv.cast (R := fun x : Points X ↦ ULift.{u + 1} (X.residueField x))
      (PrimeDivisor.spaceGenericPoint_map Z).symm).toRingHom.comp
        (henselianLocalRingToResidueField Z.genericPoint))

/-- Use this same ring identification for the fraction and its residue. -/
def residueOnSections (Z : PrimeDivisor X)
    (N : EtaleNeighborhood X Z.genericPoint)
    (hN : IsAffine N.scheme ∧ Points.mapOfOver N.hom ⁻¹' {Z.genericPoint} = {N.point} ∧ N.IsElementary)
    (R : Type u) [CommRing R] [Algebra (N.scheme.presheaf.stalk N.point) R]
    [IsHenselizationOf (N.scheme.presheaf.stalk N.point) R]
    (e : henselianLocalRing X Z.genericPoint ≃+* identityRing Z N hN R) :
    Γ((henselizationOver X Z.genericPoint N hN R).left, ⊤) →+* (residuePoint Z).K :=
  ULift.ringEquiv.toRingHom.comp
    ((residueCoefficient Z).comp (e.symm.toRingHom.comp ULift.ringEquiv.symm.toRingHom))

/-- Actual Spec of that coefficient map, followed by the affine identification. -/
def residueSchemeMap (Z : PrimeDivisor X)
    (N : EtaleNeighborhood X Z.genericPoint)
    (hN : IsAffine N.scheme ∧ Points.mapOfOver N.hom ⁻¹' {Z.genericPoint} = {N.point} ∧ N.IsElementary)
    (R : Type u) [CommRing R] [Algebra (N.scheme.presheaf.stalk N.point) R]
    [IsHenselizationOf (N.scheme.presheaf.stalk N.point) R]
    (e : henselianLocalRing X Z.genericPoint ≃+* identityRing Z N hN R) :
    (residuePoint Z).overObj.left ⟶ (henselizationOver X Z.genericPoint N hN R).left :=
  Spec.map (CommRingCat.ofHom (residueOnSections Z N hN R e)) ≫
    (Spec (CommRingCat.of R)).isoSpec.inv

private theorem topToIdentity_over_w (H : Over S) :
    (Scheme.topIso H.left).hom ≫ H.hom =
      (Modules.RestrictToScheme.siteObject H ⊤).left.hom := sorry

private theorem topToIdentity_w (H : Over S) :
    ofOverMap (Over.homMk (Scheme.topIso H.left).hom (topToIdentity_over_w H)) ≫
      (smallEtaleSite.id H).hom = (Modules.RestrictToScheme.siteObject H ⊤).hom := sorry

/-- The top open of a represented scheme maps to its identity étale chart. -/
@[no_expose] def topToIdentity (H : Over S) :
    Modules.RestrictToScheme.siteObject H ⊤ ⟶ smallEtaleSite.id H :=
  MorphismProperty.CostructuredArrow.homMk
    (Over.homMk (Scheme.topIso H.left).hom (topToIdentity_over_w H))
    trivial (topToIdentity_w H)

/-- Read the specified identity-chart module value as the corresponding section. -/
def identitySection (H : Over S) (M : (ofOver H).Modules)
    (t : (Modules.liftModule M).val.obj (op (smallEtaleSite.id H))) :
    Γ((Modules.restrictToScheme H).obj M, ⊤) :=
  (Modules.RestrictToScheme.sectionEquiv H M ⊤).symm
    (M.val.map (topToIdentity H).op t.down)

/-- A local presentation of a meromorphic section by a spanning henselian generator,
a nonzerodivisor ratio, and compatible residue triangles in the same coordinates. -/
structure LocalPresentation {L : X.Modules} [isInvertibleObject L]
    (s : meromorphicSections X L) (Z : PrimeDivisor X) where

  /-- The affine elementary neighbourhood used by the presentation. -/
  neighborhood : EtaleNeighborhood X Z.genericPoint
  /-- Affineness, singleton fibre, and elementarity of the neighbourhood. -/
  neighborhood_spec : IsAffine neighborhood.scheme ∧
    Points.mapOfOver neighborhood.hom ⁻¹' {Z.genericPoint} = {neighborhood.point} ∧ neighborhood.IsElementary
  /-- A supplied henselization ring. -/
  ring : Type u
  /-- The ring operations on the supplied henselization. -/
  ringStructure : CommRing ring
  /-- The structural algebra over the neighbourhood stalk. -/
  algebraStructure : @Algebra (neighborhood.scheme.presheaf.stalk neighborhood.point) ring _ ringStructure.toSemiring
  /-- The supplied algebra is a henselization. -/
  henselizationStructure : @IsHenselizationOf
    (neighborhood.scheme.presheaf.stalk neighborhood.point) _ _ ring ringStructure algebraStructure
  /-- The same henselian coordinates are used for both the fraction and residue. -/
  ringEquiv : henselianLocalRing X Z.genericPoint ≃+* (@identityRing S X inferInstance Z neighborhood neighborhood_spec ring ringStructure algebraStructure henselizationStructure)
  /-- The spanning generator of the pulled-back invertible module. -/
  generator : (Modules.liftModule ((@henselianModule S X inferInstance L Z neighborhood neighborhood_spec ring ringStructure algebraStructure henselizationStructure))).val.obj ((@identityChart S X inferInstance Z neighborhood neighborhood_spec ring ringStructure algebraStructure henselizationStructure))
  /-- The actual generator spans the rank-one module over its local ring. -/
  generator_span : Submodule.span ((@identityRing S X inferInstance Z neighborhood neighborhood_spec ring ringStructure algebraStructure henselizationStructure)) {generator} = ⊤
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
    (regularStructureSections ((@henselizationSpace S X inferInstance Z.genericPoint neighborhood neighborhood_spec ring ringStructure algebraStructure henselizationStructure))).obj ((@identityChart S X inferInstance Z neighborhood neighborhood_spec ring ringStructure algebraStructure henselizationStructure))
  /-- The ratio times this generator is the actual pulled germ of s. -/
  germ_eq :
    (CategoryTheory.toSheafify (smallEtaleTopology ((@henselizationSpace S X inferInstance Z.genericPoint neighborhood neighborhood_spec ring ringStructure algebraStructure henselizationStructure)))
      (meromorphicSectionPresheaf ((@henselizationSpace S X inferInstance Z.genericPoint neighborhood neighborhood_spec ring ringStructure algebraStructure henselizationStructure))
        ((@henselianModule S X inferInstance L Z neighborhood neighborhood_spec ring ringStructure algebraStructure henselizationStructure))).presheaf).app ((@identityChart S X inferInstance Z neighborhood neighborhood_spec ring ringStructure algebraStructure henselizationStructure))
      (LocalizedModule.mk (ringEquiv numerator • generator)
        ⟨ringEquiv denominator, denominator_section_regular⟩) =
      sections.eval (@MeromorphicConstruction.Pullback.pullback S _ X
      (@fromHenselization S X inferInstance Z.genericPoint neighborhood neighborhood_spec ring ringStructure algebraStructure henselizationStructure)
      (@instPullbacksMeromorphicFunctionsDefined_of_flat S _ X _ (@Henselization.flat_fromNeighborhood S X neighborhood.toOver neighborhood.hom
      neighborhood.toSite.prop neighborhood.point ring ringStructure algebraStructure henselizationStructure)) L s)
        ((@identityChart S X inferInstance Z neighborhood neighborhood_spec ring ringStructure algebraStructure henselizationStructure))
  /-- The induced Spec residue map has the original base structure. -/
  residue_over_base : (@residueSchemeMap S X inferInstance Z neighborhood neighborhood_spec ring ringStructure algebraStructure henselizationStructure) ringEquiv ≫
    ((@henselizationOver S X inferInstance Z.genericPoint neighborhood neighborhood_spec ring ringStructure algebraStructure henselizationStructure)).hom = (residuePoint Z).overObj.hom
  /-- It is the residue point over X, not a second unrelated coordinate choice. -/
  residue_over_X :
    ofOverMap (Over.homMk ((@residueSchemeMap S X inferInstance Z neighborhood neighborhood_spec ring ringStructure algebraStructure henselizationStructure) ringEquiv) residue_over_base) ≫
      (@fromHenselization S X inferInstance Z.genericPoint neighborhood neighborhood_spec ring ringStructure algebraStructure henselizationStructure) = (residuePoint Z).hom ≫ Z.ι

namespace LocalPresentation
variable {L : X.Modules} [isInvertibleObject L]
    {s : meromorphicSections X L} {Z : PrimeDivisor X}

/-- Construct a local presentation from its supplied neighbourhood, henselization,
generator, ratio, and compatible residue triangles. -/
def ofData
    (neighborhood : EtaleNeighborhood X Z.genericPoint)
    (neighborhood_spec : IsAffine neighborhood.scheme ∧
    Points.mapOfOver neighborhood.hom ⁻¹' {Z.genericPoint} = {neighborhood.point} ∧ neighborhood.IsElementary)
    (ring : Type u)
    (ringStructure : CommRing ring)
    (algebraStructure : @Algebra (neighborhood.scheme.presheaf.stalk neighborhood.point) ring _ ringStructure.toSemiring)
    (henselizationStructure : @IsHenselizationOf
    (neighborhood.scheme.presheaf.stalk neighborhood.point) _ _ ring ringStructure algebraStructure)
    (ringEquiv : henselianLocalRing X Z.genericPoint ≃+* (@identityRing S X inferInstance Z neighborhood neighborhood_spec ring ringStructure algebraStructure henselizationStructure))
    (generator : (Modules.liftModule ((@henselianModule S X inferInstance L Z neighborhood neighborhood_spec ring ringStructure algebraStructure henselizationStructure))).val.obj ((@identityChart S X inferInstance Z neighborhood neighborhood_spec ring ringStructure algebraStructure henselizationStructure)))
    (generator_span : Submodule.span ((@identityRing S X inferInstance Z neighborhood neighborhood_spec ring ringStructure algebraStructure henselizationStructure)) {generator} = ⊤)
    (numerator : henselianLocalRing X Z.genericPoint)
    (denominator : henselianLocalRing X Z.genericPoint)
    (numerator_regular : numerator ∈ nonZeroDivisors (henselianLocalRing X Z.genericPoint))
    (denominator_regular : denominator ∈ nonZeroDivisors (henselianLocalRing X Z.genericPoint))
    (denominator_section_regular : ringEquiv denominator ∈
    (regularStructureSections ((@henselizationSpace S X inferInstance Z.genericPoint neighborhood neighborhood_spec ring ringStructure algebraStructure henselizationStructure))).obj ((@identityChart S X inferInstance Z neighborhood neighborhood_spec ring ringStructure algebraStructure henselizationStructure)))
    (germ_eq : (CategoryTheory.toSheafify (smallEtaleTopology ((@henselizationSpace S X inferInstance Z.genericPoint neighborhood neighborhood_spec ring ringStructure algebraStructure henselizationStructure)))
    (meromorphicSectionPresheaf ((@henselizationSpace S X inferInstance Z.genericPoint neighborhood neighborhood_spec ring ringStructure algebraStructure henselizationStructure))
    ((@henselianModule S X inferInstance L Z neighborhood neighborhood_spec ring ringStructure algebraStructure henselizationStructure))).presheaf).app ((@identityChart S X inferInstance Z neighborhood neighborhood_spec ring ringStructure algebraStructure henselizationStructure))
    (LocalizedModule.mk (ringEquiv numerator • generator)
    ⟨ringEquiv denominator, denominator_section_regular⟩) =
    sections.eval (@MeromorphicConstruction.Pullback.pullback S _ X
    (@fromHenselization S X inferInstance Z.genericPoint neighborhood neighborhood_spec ring ringStructure algebraStructure henselizationStructure)
    (@instPullbacksMeromorphicFunctionsDefined_of_flat S _ X _ (@Henselization.flat_fromNeighborhood S X neighborhood.toOver neighborhood.hom
    neighborhood.toSite.prop neighborhood.point ring ringStructure algebraStructure henselizationStructure)) L s)
    ((@identityChart S X inferInstance Z neighborhood neighborhood_spec ring ringStructure algebraStructure henselizationStructure)))
    (residue_over_base : (@residueSchemeMap S X inferInstance Z neighborhood neighborhood_spec ring ringStructure algebraStructure henselizationStructure) ringEquiv ≫
    ((@henselizationOver S X inferInstance Z.genericPoint neighborhood neighborhood_spec ring ringStructure algebraStructure henselizationStructure)).hom = (residuePoint Z).overObj.hom)
    (residue_over_X : ofOverMap (Over.homMk ((@residueSchemeMap S X inferInstance Z neighborhood neighborhood_spec ring ringStructure algebraStructure henselizationStructure) ringEquiv) residue_over_base) ≫
    (@fromHenselization S X inferInstance Z.genericPoint neighborhood neighborhood_spec ring ringStructure algebraStructure henselizationStructure) = (residuePoint Z).hom ≫ Z.ι) : LocalPresentation s Z :=
  ⟨neighborhood, neighborhood_spec, ring, ringStructure, algebraStructure, henselizationStructure, ringEquiv, generator, generator_span, numerator, denominator, numerator_regular, denominator_regular, denominator_section_regular, germ_eq, residue_over_base, residue_over_X⟩

private theorem fraction_laws (d : LocalPresentation s Z) :
    (IsLocalization.mk' (FractionRing (henselianLocalRing X Z.genericPoint))
      d.numerator ⟨d.denominator, d.denominator_regular⟩) *
      IsLocalization.mk' _ d.denominator ⟨d.numerator, d.numerator_regular⟩ = 1 ∧
    (IsLocalization.mk' (FractionRing (henselianLocalRing X Z.genericPoint))
      d.denominator ⟨d.numerator, d.numerator_regular⟩) *
      IsLocalization.mk' _ d.numerator ⟨d.denominator, d.denominator_regular⟩ = 1 := sorry

/-- The actual ratio of this presentation's regular numerator and denominator. -/
@[no_expose] def fraction (d : LocalPresentation s Z) :
    (FractionRing (henselianLocalRing X Z.genericPoint))ˣ :=
  { val := IsLocalization.mk' _ d.numerator ⟨d.denominator, d.denominator_regular⟩
    inv := IsLocalization.mk' _ d.denominator ⟨d.numerator, d.numerator_regular⟩
    val_inv := (fraction_laws d).1
    inv_val := (fraction_laws d).2 }

/-- The concrete ratio and the residue image use this very same generator
and ring identification of the local presentation. -/
theorem fraction_isRatio (d : LocalPresentation s Z) :
    MeromorphicSection.IsRatioOfPulledGerm s Z (d.fraction :
      FractionRing (henselianLocalRing X Z.genericPoint)) := by
  refine ⟨d.neighborhood, d.neighborhood_spec, d.ring, d.ringStructure,
    d.algebraStructure, d.henselizationStructure, d.generator, d.numerator, d.denominator, d.denominator_regular,
    d.ringEquiv, d.denominator_section_regular, d.numerator_regular,
    d.generator_span, ?_, d.germ_eq⟩
  rfl

/-- The same residue morphism regarded over the original base. -/
def residueOver (d : LocalPresentation s Z) :
    (residuePoint Z).overObj ⟶ (@henselizationOver S X inferInstance Z.genericPoint d.neighborhood d.neighborhood_spec d.ring d.ringStructure d.algebraStructure d.henselizationStructure) :=
  Over.homMk ((@residueSchemeMap S X inferInstance Z d.neighborhood d.neighborhood_spec d.ring d.ringStructure d.algebraStructure d.henselizationStructure d.ringEquiv)) d.residue_over_base

/-- Common carrier: the original module pulled back to the specified residue point. -/
abbrev fibreSections (L : X.Modules) (Z : PrimeDivisor X) : Type u :=
  Γ((Modules.restrictToScheme (residuePoint Z).overObj).obj
    ((Modules.pullback ((residuePoint Z).hom ≫ Z.ι)).obj L), ⊤)

/-- Pull the same generator along its actual Spec residue map, then the
canonical composition comparison and its actual commuting triangle. -/
def generatorImage (d : LocalPresentation s Z) : fibreSections L Z :=
  let value := (Scheme.Modules.globalSectionsMap
      (Modules.RestrictToScheme.compositePullbackComparison
        ((@fromHenselization S X inferInstance Z.genericPoint d.neighborhood d.neighborhood_spec d.ring d.ringStructure d.algebraStructure d.henselizationStructure)) d.residueOver L)).hom
    ((Scheme.Modules.globalSectionsPullback d.residueOver.left
      ((Modules.restrictToScheme ((@henselizationOver S X inferInstance Z.genericPoint d.neighborhood d.neighborhood_spec d.ring d.ringStructure d.algebraStructure d.henselizationStructure))).obj
        ((@henselianModule S X inferInstance L Z d.neighborhood d.neighborhood_spec d.ring d.ringStructure d.algebraStructure d.henselizationStructure)))).hom
      (identitySection ((@henselizationOver S X inferInstance Z.genericPoint d.neighborhood d.neighborhood_spec d.ring d.ringStructure d.algebraStructure d.henselizationStructure)) ((@henselianModule S X inferInstance L Z d.neighborhood d.neighborhood_spec d.ring d.ringStructure d.algebraStructure d.henselizationStructure)) d.generator))
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

/-- Restricting the recovered section gives the residue image of its generator. -/
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

end AlgebraicGeometry.AlgebraicSpace
