/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Deformation.Difference
public import ReasLib.CategoryTheory.Sites.LocalSectionDescent

/-!
# Difference derivations of lifts of algebraic-space morphisms

The ordered structure-map difference lifts to the conormal sheaf, descends along
the locally surjective restriction, and transposes to a relative derivation.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ConcreteCategory AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace.Thickening
open Sheaf.InternalModule RingedSite.ToposHom
noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.Deformation

variable {S : Scheme.{u}}

/-- The additive ambient target coefficients after inverse image to the reduced source. -/
private abbrev differenceSource {X Y Y' : AlgebraicSpace S} (a : X ⟶ Y) (iY : Y ⟶ Y') :=
  (EtaleAdditive.restriction X).obj ((forgetSpacesRing X).obj (inverseImageClosedStructureSheaf a iY))

/-- The restriction from ambient target coefficients to the inverse image of reduced ones. -/
private def differenceRestriction {X Y Y' : AlgebraicSpace S} (a : X ⟶ Y) (iY : Y ⟶ Y') :
    differenceSource a iY ⟶
      (EtaleAdditive.inverseImage a).obj
        ((sheafCompose (smallEtaleTopology Y) (forget₂ RingCat AddCommGrpCat.{u})).obj
          (structureSheaf Y)) :=
  pulledRestriction a iY ≫ (restrictInverseImageIso a).hom

section CommonReduction

variable {X X' Y Y' : AlgebraicSpace S}
variable (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y) (a' b' : X' ⟶ Y')
variable [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
variable (sqA : CommSq a iX iY a') (sqB : CommSq a iX iY b')

/-- Reconstruct a section from the graph of the ordered difference in the conormal
inclusion, taking zero outside the image. -/
private def differenceConormalSection (U : (smallEtaleSite X)ᵒᵖ)
    (t : (differenceSource a iY).obj.obj U) : (differenceCoefficient iX).obj.obj U := by
  classical
  exact if h : ∃ m : (differenceCoefficient iX).obj.obj U,
      (conormalInclusion iX).hom.app U m =
        (structureMapDifference_restrict iX iY a a' b' sqA.w.symm sqB.w.symm).hom.app U t
  then h.choose else 0

/-- The difference has precisely the conormal section prescribed by the section graph. -/
private theorem differenceConormalSection_spec (U : (smallEtaleSite X)ᵒᵖ)
    (t : (differenceSource a iY).obj.obj U) :
    (conormalInclusion iX).hom.app U
        (differenceConormalSection iX iY a a' b' sqA sqB U t) =
      (structureMapDifference_restrict iX iY a a' b' sqA.w.symm sqB.w.symm).hom.app U t :=
  sorry

/-- The actual conormal-section functions assemble to an additive sheaf morphism. -/
private def differenceConormal : differenceSource a iY ⟶ differenceCoefficient iX :=
  ⟨{ app := fun U ↦ AddCommGrpCat.ofHom
        { toFun := differenceConormalSection iX iY a a' b' sqA sqB U
          map_zero' := sorry
          map_add' := sorry }
     naturality := sorry }⟩

/-- The component function of the lifted additive difference is the specified section graph. -/
private theorem differenceConormal_apply (U : (smallEtaleSite X)ᵒᵖ)
    (t : (differenceSource a iY).obj.obj U) :
    (differenceConormal iX iY a a' b' sqA sqB).hom.app U t =
      differenceConormalSection iX iY a a' b' sqA sqB U t := rfl

end CommonReduction

/-- Restriction to the reduced target is locally surjective after inverse image. -/
private theorem differenceRestrictionTypes_isLocallySurjective
    {X Y Y' : AlgebraicSpace S} (a : X ⟶ Y) (iY : Y ⟶ Y')
    [IsFirstOrderThickening iY] :
    Presheaf.IsLocallySurjective (smallEtaleTopology X)
      (((sheafCompose (smallEtaleTopology X) (forget AddCommGrpCat.{u})).map
        (differenceRestriction a iY)).hom) := sorry

section Descent

variable {X X' Y Y' : AlgebraicSpace S}
variable (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y) (a' b' : X' ⟶ Y')
variable [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
variable (sqA : CommSq a iX iY a') (sqB : CommSq a iX iY b')
variable (hconormal : Hom.Conormal.map sqA = Hom.Conormal.map sqB)

include hconormal in
/-- Equal induced conormal maps make the lifted difference constant on restriction fibres. -/
private theorem differenceConormal_fibre :
    ∀ (U : (smallEtaleSite X)ᵒᵖ) (t s : (differenceSource a iY).obj.obj U),
      (differenceRestriction a iY).hom.app U t =
        (differenceRestriction a iY).hom.app U s →
      (differenceConormal iX iY a a' b' sqA sqB).hom.app U t =
        (differenceConormal iX iY a a' b' sqA sqB).hom.app U s := sorry

/-- Descend the actual conormal-section family by gluing over the restriction image sieve. -/
private def differenceDescendedType :
    ((sheafCompose (smallEtaleTopology X) (forget AddCommGrpCat.{u})).obj
      ((EtaleAdditive.inverseImage a).obj
        ((sheafCompose (smallEtaleTopology Y) (forget₂ RingCat AddCommGrpCat.{u})).obj
          (structureSheaf Y)))).obj ⟶
      ((sheafCompose (smallEtaleTopology X) (forget AddCommGrpCat.{u})).obj
        (differenceCoefficient iX)).obj :=
  Presheaf.LocalSectionDescent.descend (smallEtaleTopology X)
    (hη := differenceRestrictionTypes_isLocallySurjective a iY)
    (((sheafCompose (smallEtaleTopology X) (forget AddCommGrpCat.{u})).map
      (differenceRestriction a iY)).hom)
    (((sheafCompose (smallEtaleTopology X) (forget AddCommGrpCat.{u})).map
      (differenceConormal iX iY a a' b' sqA sqB)).hom)
    (((sheafCompose (smallEtaleTopology X) (forget AddCommGrpCat.{u})).obj
      (differenceCoefficient iX)).property)
    (differenceConormal_fibre iX iY a a' b' sqA sqB hconormal)

/-- The descended section functions retain their actual additive structures. -/
private def differenceDescended :
    (EtaleAdditive.inverseImage a).obj
        ((sheafCompose (smallEtaleTopology Y) (forget₂ RingCat AddCommGrpCat.{u})).obj
          (structureSheaf Y)) ⟶ differenceCoefficient iX :=
  ⟨{ app := fun U ↦ AddCommGrpCat.ofHom
        { toFun := (differenceDescendedType iX iY a a' b' sqA sqB hconormal).app U
          map_zero' := sorry
          map_add' := sorry }
     naturality := sorry }⟩

/-- The actual additive adjunction and forgetful inverse provide the downstairs section map. -/
def differenceAdjoint :
    (sheafCompose (smallEtaleTopology Y) (forget₂ RingCat AddCommGrpCat.{u})).obj
        (structureSheaf Y) ⟶
      (SheafOfModules.toSheaf (structureSheaf Y)).obj
        ((Modules.pushforward a).obj (Hom.conormalSheaf iX)) :=
  ((EtaleAdditive.adjunction a).homEquiv _ _
    (differenceDescended iX iY a a' b' sqA sqB hconormal)) ≫
    modulePushforwardForgetAddInv a (Hom.conormalSheaf iX)

end Descent

/-- The relative derivation is specified by actual structure-map differences, conormal
sections and local sheaf descent. The two lifts are morphisms over the base. -/
def differenceDerivation {B X X' Y Y' : AlgebraicSpace S}
    (sY : Y ⟶ B) (sX' : X' ⟶ B) (sY' : Y' ⟶ B)
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y) (a' b' : X' ⟶ Y')
    [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (hY : iY ≫ sY' = sY) (ha : a ≫ sY = iX ≫ sX')
    (ha' : a' ≫ sY' = sX') (hb' : b' ≫ sY' = sX')
    (sqA : CommSq a iX iY a') (sqB : CommSq a iX iY b')
    (hconormal : Hom.Conormal.map sqA = Hom.Conormal.map sqB) :
    Hom.derivations sY ((Modules.pushforward a).obj (Hom.conormalSheaf iX)) where
  d {U} := (differenceAdjoint iX iY a a' b' sqA sqB hconormal).hom.app U |>.hom
  d_mul := sorry
  d_map := sorry
  d_app := sorry

/-- Recover the differential parameter by the canonical Kähler descent and the actual
module pullback/pushforward adjunction, applied to the specified difference derivation. -/
def differenceParameter {B X X' Y Y' : AlgebraicSpace S}
    (sY : Y ⟶ B) (sX' : X' ⟶ B) (sY' : Y' ⟶ B)
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y) (a' b' : X' ⟶ Y')
    [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (hY : iY ≫ sY' = sY) (ha : a ≫ sY = iX ≫ sX')
    (ha' : a' ≫ sY' = sX') (hb' : b' ≫ sY' = sX')
    (sqA : CommSq a iX iY a') (sqB : CommSq a iX iY b')
    (hconormal : Hom.Conormal.map sqA = Hom.Conormal.map sqB) :
    (Modules.pullback a).obj (Hom.relativeDifferentials sY) ⟶ Hom.conormalSheaf iX :=
  ((Modules.pullbackPushforwardAdjunction a).homEquiv _ _).symm
    (SheafOfModules.RingedSite.relativeDifferentialDesc
      (commInverseImageStructureSheafMap sY)
      (differenceDerivation sY sX' sY' iX iY a a' b'
        hY ha ha' hb' sqA sqB hconormal))

/-- The specified derivation recovers the original ordered difference. -/
theorem differenceDerivation_spec {B X X' Y Y' : AlgebraicSpace S}
    (sY : Y ⟶ B) (sX' : X' ⟶ B) (sY' : Y' ⟶ B)
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y) (a' b' : X' ⟶ Y')
    [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (hY : iY ≫ sY' = sY) (ha : a ≫ sY = iX ≫ sX')
    (ha' : a' ≫ sY' = sX') (hb' : b' ≫ sY' = sX')
    (sqA : CommSq a iX iY a') (sqB : CommSq a iX iY b')
    (hconormal : Hom.Conormal.map sqA = Hom.Conormal.map sqB) :
    structureMapDifference_restrict iX iY a a' b' sqA.w.symm sqB.w.symm =
      factorizationMap sY iX iY a
        (differenceDerivation sY sX' sY' iX iY a a' b'
          hY ha ha' hb' sqA sqB hconormal) := sorry


/-- Two morphisms of first-order thickenings over `B` with a common reduced map and
equal induced conormal maps differ by an `𝒪_B`-derivation
`𝒪_Y ⟶ a_* C_{X/X'}`. -/
theorem exists_differenceDerivation {B X X' Y Y' : AlgebraicSpace S}
    (sY : Y ⟶ B) (sX' : X' ⟶ B) (sY' : Y' ⟶ B)
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y) (a' b' : X' ⟶ Y')
    [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (hY : iY ≫ sY' = sY) (ha : a ≫ sY = iX ≫ sX')
    (ha' : a' ≫ sY' = sX') (hb' : b' ≫ sY' = sX')
    (sqA : CommSq a iX iY a') (sqB : CommSq a iX iY b')
    (hconormal : Hom.Conormal.map sqA = Hom.Conormal.map sqB) :
    ∃ D : Hom.derivations sY ((Modules.pushforward a).obj (Hom.conormalSheaf iX)),
      structureMapDifference_restrict iX iY a a' b' sqA.w.symm sqB.w.symm =
        factorizationMap sY iX iY a D :=
  ⟨differenceDerivation sY sX' sY' iX iY a a' b' hY ha ha' hb' sqA sqB hconormal,
    differenceDerivation_spec sY sX' sY' iX iY a a' b'
      hY ha ha' hb' sqA sqB hconormal⟩

end AlgebraicGeometry.AlgebraicSpace.Hom.Deformation
