/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Prime
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.FieldRamification

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- A scheme and an open subset have discrete-valuation boundary stalks at all disjoint prime
divisors. -/
class HasDVRBoundary (X : Scheme.{u}) (U : X.Opens) : Prop where
  /-- The stalk at every boundary prime-divisor generic point is a domain. -/
  boundaryStalk_domain : ∀ (Z : PrimeDivisor X),
    Disjoint (Z.support : Set X) (U : Set X) →
      IsDomain (X.presheaf.stalk Z.genericPoint)
  /-- The stalk at every boundary prime-divisor generic point is a DVR. -/
  boundaryStalk_dvr : ∀ (Z : PrimeDivisor X),
    (hZ : Disjoint (Z.support : Set X) (U : Set X)) →
      @IsDiscreteValuationRing (X.presheaf.stalk Z.genericPoint) inferInstance
        (boundaryStalk_domain Z hZ)

/-- The two boundary-stalk conditions supplied by `HasDVRBoundary`. -/
theorem HasDVRBoundary.spec {X : Scheme.{u}} {U : X.Opens}
    (h : HasDVRBoundary X U) :
    ∀ (Z : PrimeDivisor X) (hZ : Disjoint (Z.support : Set X) (U : Set X)),
      IsDomain (X.presheaf.stalk Z.genericPoint) ∧
        @IsDiscreteValuationRing (X.presheaf.stalk Z.genericPoint) inferInstance
          (h.boundaryStalk_domain Z hZ) := sorry

namespace FiniteEtale

/-- The map from the fraction-field spectrum at a prime-divisor generic point to `X`. -/
noncomputable def genericMap {X : Scheme.{u}} (Z : PrimeDivisor X) :
    Spec (CommRingCat.of (FractionRing (X.presheaf.stalk Z.genericPoint))) ⟶ X :=
  Spec.map (CommRingCat.ofHom
      (algebraMap (X.presheaf.stalk Z.genericPoint)
        (FractionRing (X.presheaf.stalk Z.genericPoint)))) ≫
    X.fromSpecStalk Z.genericPoint

/-- The defining composite for `FiniteEtale.genericMap`. -/
theorem genericMap_spec {X : Scheme.{u}} (Z : PrimeDivisor X) :
    genericMap Z =
      Spec.map (CommRingCat.ofHom
          (algebraMap (X.presheaf.stalk Z.genericPoint)
            (FractionRing (X.presheaf.stalk Z.genericPoint)))) ≫
        X.fromSpecStalk Z.genericPoint := sorry

/-- The finite-etale cover's generic boundary fiber, bundled as an algebra over the fraction
field of the boundary stalk. -/
noncomputable def boundaryFiber {X : Scheme.{u}} {U : X.Opens}
    (Y : Scheme.FiniteEtale U.toScheme) (Z : PrimeDivisor X) :
    CommAlgCat (FractionRing (X.presheaf.stalk Z.genericPoint)) :=
  Scheme.Hom.globalSectionsAlg
    (pullback.snd (Y.hom ≫ U.ι) (genericMap Z))

/-- The boundary fiber is the global-sections algebra of the pulled-back cover over the generic
point spectrum. -/
theorem boundaryFiber_spec {X : Scheme.{u}} {U : X.Opens}
    (Y : Scheme.FiniteEtale U.toScheme) (Z : PrimeDivisor X) :
    boundaryFiber Y Z =
      Scheme.Hom.globalSectionsAlg
        (pullback.snd (Y.hom ≫ U.ι) (genericMap Z)) := sorry

namespace BoundaryFiber
namespace Branch

variable {X : Scheme.{u}} {U : X.Opens}
variable (Y : Scheme.FiniteEtale U.toScheme) (Z : PrimeDivisor X)

/-- The quotient ring selected by a maximal branch of a boundary fiber. -/
abbrev ring (m : MaximalSpectrum (boundaryFiber Y Z)) :=
  (boundaryFiber Y Z) ⧸ m.asIdeal

/-- The canonical field structure on a maximal boundary-fiber branch. -/
noncomputable abbrev field (m : MaximalSpectrum (boundaryFiber Y Z)) : Field (ring Y Z m) :=
  Ideal.Quotient.field m.asIdeal

/-- The algebra from the boundary stalk's fraction field to a maximal boundary-fiber branch. -/
noncomputable abbrev fractionAlgebra (m : MaximalSpectrum (boundaryFiber Y Z)) :
    Algebra (FractionRing (X.presheaf.stalk Z.genericPoint)) (ring Y Z m) :=
  RingHom.toAlgebra
    ((Ideal.Quotient.mk m.asIdeal).comp
      (algebraMap (FractionRing (X.presheaf.stalk Z.genericPoint)) (boundaryFiber Y Z)))

/-- The algebra from the boundary stalk to a maximal boundary-fiber branch. -/
noncomputable abbrev baseAlgebra (m : MaximalSpectrum (boundaryFiber Y Z)) :
    Algebra (X.presheaf.stalk Z.genericPoint) (ring Y Z m) :=
  RingHom.toAlgebra
    ((Ideal.Quotient.mk m.asIdeal).comp
      ((algebraMap (FractionRing (X.presheaf.stalk Z.genericPoint)) (boundaryFiber Y Z)).comp
        (algebraMap (X.presheaf.stalk Z.genericPoint)
          (FractionRing (X.presheaf.stalk Z.genericPoint)))))

/-- The fraction-field and base-stalk algebra maps on a branch satisfy the scalar-tower law. -/
theorem isScalarTower (m : MaximalSpectrum (boundaryFiber Y Z)) :
    @IsScalarTower (X.presheaf.stalk Z.genericPoint)
      (FractionRing (X.presheaf.stalk Z.genericPoint)) (ring Y Z m)
      inferInstance (fractionAlgebra Y Z m).toSMul (baseAlgebra Y Z m).toSMul := sorry

/-- The named quotient field and algebra maps form a usable boundary branch with scalar tower. -/
theorem spec (m : MaximalSpectrum (boundaryFiber Y Z)) :
    @IsScalarTower (X.presheaf.stalk Z.genericPoint)
      (FractionRing (X.presheaf.stalk Z.genericPoint)) (ring Y Z m)
      inferInstance (fractionAlgebra Y Z m).toSMul (baseAlgebra Y Z m).toSMul :=
  isScalarTower Y Z m

end Branch
end BoundaryFiber

/-- A boundary branch is unramified when its fraction-field extension is unramified over the
boundary DVR. -/
abbrev unramifiedBranch {X : Scheme.{u}} {U : X.Opens}
    (h : HasDVRBoundary X U) (Y : Scheme.FiniteEtale U.toScheme)
    (Z : PrimeDivisor X) (hZ : Disjoint (Z.support : Set X) (U : Set X))
    (m : MaximalSpectrum (boundaryFiber Y Z)) : Prop :=
  @DVR.Field.IsUnramified
    (X.presheaf.stalk Z.genericPoint)
    (FractionRing (X.presheaf.stalk Z.genericPoint))
    (BoundaryFiber.Branch.ring Y Z m)
    inferInstance (h.boundaryStalk_domain Z hZ) (h.boundaryStalk_dvr Z hZ)
    (@FractionRing.field (X.presheaf.stalk Z.genericPoint) inferInstance
      (h.boundaryStalk_domain Z hZ)) inferInstance inferInstance
    (BoundaryFiber.Branch.field Y Z m)
    (BoundaryFiber.Branch.baseAlgebra Y Z m)
    (BoundaryFiber.Branch.fractionAlgebra Y Z m)
    (BoundaryFiber.Branch.isScalarTower Y Z m)

/-- A boundary branch is tamely ramified when its fraction-field extension is tamely ramified over
the boundary DVR. -/
abbrev tameBranch {X : Scheme.{u}} {U : X.Opens}
    (h : HasDVRBoundary X U) (Y : Scheme.FiniteEtale U.toScheme)
    (Z : PrimeDivisor X) (hZ : Disjoint (Z.support : Set X) (U : Set X))
    (m : MaximalSpectrum (boundaryFiber Y Z)) : Prop :=
  @DVR.Field.IsTamelyRamified
    (X.presheaf.stalk Z.genericPoint)
    (FractionRing (X.presheaf.stalk Z.genericPoint))
    (BoundaryFiber.Branch.ring Y Z m)
    inferInstance (h.boundaryStalk_domain Z hZ) (h.boundaryStalk_dvr Z hZ)
    (@FractionRing.field (X.presheaf.stalk Z.genericPoint) inferInstance
      (h.boundaryStalk_domain Z hZ)) inferInstance inferInstance
    (BoundaryFiber.Branch.field Y Z m)
    (BoundaryFiber.Branch.baseAlgebra Y Z m)
    (BoundaryFiber.Branch.fractionAlgebra Y Z m)
    (BoundaryFiber.Branch.isScalarTower Y Z m)

/-- A finite-etale cover of `U` is unramified over `X` in codimension one when every maximal
branch of every boundary generic fiber is unramified over its boundary DVR. -/
def IsUnramifiedInCodimensionOne {X : Scheme.{u}} (U : X.Opens)
    (hU : Dense (U : Set X)) [h : HasDVRBoundary X U]
    (Y : Scheme.FiniteEtale U.toScheme) : Prop :=
  ∀ (Z : PrimeDivisor X) (hZ : Disjoint (Z.support : Set X) (U : Set X))
    (m : MaximalSpectrum (boundaryFiber Y Z)), unramifiedBranch h Y Z hZ m

/-- A finite-etale cover of `U` is tamely ramified over `X` in codimension one when every maximal
branch of every boundary generic fiber is tamely ramified over its boundary DVR. -/
def IsTamelyRamifiedInCodimensionOne {X : Scheme.{u}} (U : X.Opens)
    (hU : Dense (U : Set X)) [h : HasDVRBoundary X U]
    (Y : Scheme.FiniteEtale U.toScheme) : Prop :=
  ∀ (Z : PrimeDivisor X) (hZ : Disjoint (Z.support : Set X) (U : Set X))
    (m : MaximalSpectrum (boundaryFiber Y Z)), tameBranch h Y Z hZ m

/-- The branchwise characterization of unramifiedness in codimension one. -/
theorem isUnramifiedInCodimensionOne_iff {X : Scheme.{u}} (U : X.Opens)
    (hU : Dense (U : Set X)) [h : HasDVRBoundary X U]
    (Y : Scheme.FiniteEtale U.toScheme) :
    IsUnramifiedInCodimensionOne U hU Y ↔
      ∀ (Z : PrimeDivisor X) (hZ : Disjoint (Z.support : Set X) (U : Set X))
        (m : MaximalSpectrum (boundaryFiber Y Z)), unramifiedBranch h Y Z hZ m := sorry

/-- The branchwise characterization of tame ramification in codimension one. -/
theorem isTamelyRamifiedInCodimensionOne_iff {X : Scheme.{u}} (U : X.Opens)
    (hU : Dense (U : Set X)) [h : HasDVRBoundary X U]
    (Y : Scheme.FiniteEtale U.toScheme) :
    IsTamelyRamifiedInCodimensionOne U hU Y ↔
      ∀ (Z : PrimeDivisor X) (hZ : Disjoint (Z.support : Set X) (U : Set X))
        (m : MaximalSpectrum (boundaryFiber Y Z)), tameBranch h Y Z hZ m := sorry

/-- Unramified boundary branches are tamely ramified boundary branches. -/
theorem IsUnramifiedInCodimensionOne.isTamelyRamified
    {X : Scheme.{u}} (U : X.Opens) (hU : Dense (U : Set X))
    [h : HasDVRBoundary X U] (Y : Scheme.FiniteEtale U.toScheme)
    (hY : IsUnramifiedInCodimensionOne U hU Y) :
    IsTamelyRamifiedInCodimensionOne U hU Y := sorry

variable {X X' : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian X']
variable (f : X' ⟶ X) (U : X.Opens)
variable (hU : Dense (U : Set X))
variable (hU' : Dense (f ⁻¹ᵁ U : Set X'))
variable [HasDVRBoundary X U]
variable [HasDVRBoundary X' (f ⁻¹ᵁ U)]

namespace IsUnramifiedInCodimensionOne

/-- Unramifiedness in codimension one is preserved by finite-etale base change under boundary
generic-point compatibility. -/
theorem baseChange
    (h_image : ∀ Z' : PrimeDivisor X',
      Disjoint (Z'.support : Set X') (f ⁻¹ᵁ U : Set X') →
        ∃ Z : PrimeDivisor X,
          Disjoint (Z.support : Set X) (U : Set X) ∧
            f Z'.genericPoint = Z.genericPoint)
    (Y : Scheme.FiniteEtale U.toScheme)
    (hY : IsUnramifiedInCodimensionOne U hU Y) :
    IsUnramifiedInCodimensionOne (f ⁻¹ᵁ U) hU'
      ((Scheme.finiteEtaleBaseChange
        (f.resLE U (f ⁻¹ᵁ U) le_rfl)).obj Y) := sorry

end IsUnramifiedInCodimensionOne

namespace IsTamelyRamifiedInCodimensionOne

/-- Tame ramification in codimension one is preserved by finite-etale base change under boundary
generic-point compatibility. -/
theorem baseChange
    (h_image : ∀ Z' : PrimeDivisor X',
      Disjoint (Z'.support : Set X') (f ⁻¹ᵁ U : Set X') →
        ∃ Z : PrimeDivisor X,
          Disjoint (Z.support : Set X) (U : Set X) ∧
            f Z'.genericPoint = Z.genericPoint)
    (Y : Scheme.FiniteEtale U.toScheme)
    (hY : IsTamelyRamifiedInCodimensionOne U hU Y) :
    IsTamelyRamifiedInCodimensionOne (f ⁻¹ᵁ U) hU'
      ((Scheme.finiteEtaleBaseChange
        (f.resLE U (f ⁻¹ᵁ U) le_rfl)).obj Y) := sorry

end IsTamelyRamifiedInCodimensionOne

end FiniteEtale

end AlgebraicGeometry.Scheme
