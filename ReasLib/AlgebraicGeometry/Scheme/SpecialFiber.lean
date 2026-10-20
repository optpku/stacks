/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.IrreducibleComponent
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Approximation
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.IdealSheaf
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Spec
public import ReasLib.AlgebraicGeometry.Scheme.IrreducibleComponent.Multiplicity
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Regular

/-!
# Special fibres as effective Cartier divisors

This file names the ideal sheaf, reduced components, and multiplicities of the closed fibre of
a scheme over a local ring.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The ideal-sheaf datum of the fibre over the closed point of a local base. -/
noncomputable def specialFiberIdeal
    {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) : X.IdealSheafData :=
  (f.fiberι (IsLocalRing.closedPoint R)).ker

/-- The special-fibre ideal is the kernel of its canonical immersion into the total space. -/
theorem specialFiberIdeal_def
    {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) :
    f.specialFiberIdeal = (f.fiberι (IsLocalRing.closedPoint R)).ker := sorry

/-- The immersion of the fibre over the closed point of a local ring is closed. -/
instance instIsClosedImmersionSpecialFiber
    {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) :
    IsClosedImmersion (f.fiberι (IsLocalRing.closedPoint R)) := sorry

/-- The subscheme cut out by the special-fibre ideal is canonically isomorphic to the fibre. -/
noncomputable def specialFiberIso
    {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) :
    f.specialFiberIdeal.subscheme ≅ f.fiber (IsLocalRing.closedPoint R) :=
  (asIso (f.fiberι (IsLocalRing.closedPoint R)).toImage).symm

/-- The special-fibre isomorphism commutes with the immersions into the total space. -/
theorem specialFiberIso_hom_fiberι
    {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) :
    f.specialFiberIso.hom ≫ f.fiberι (IsLocalRing.closedPoint R) =
      f.specialFiberIdeal.subschemeι := sorry

/-- The kernel presentation of the special fibre agrees with the pullback of the maximal-ideal
datum from the local base. -/
theorem specialFiberIdeal_eq_comap_maximalIdeal
    {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) :
    f.specialFiberIdeal =
      (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal R)).comap f := sorry

/-- A reduced irreducible component of the special fibre, regarded as an ideal-sheaf datum on
the total space. -/
noncomputable def specialFiberComponent
    {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R))
    (i : irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) :
    X.IdealSheafData :=
  (IdealSheafData.vanishingIdeal
    ((f.fiber (IsLocalRing.closedPoint R)).irreducibleComponentClosed i)).map
      (f.fiberι (IsLocalRing.closedPoint R))

/-- A special-fibre component is the ambient image of the canonical reduced component of the
scheme-theoretic fibre. -/
theorem specialFiberComponent_def
    {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R))
    (i : irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) :
    f.specialFiberComponent i =
      (IdealSheafData.vanishingIdeal
        ((f.fiber (IsLocalRing.closedPoint R)).irreducibleComponentClosed i)).map
          (f.fiberι (IsLocalRing.closedPoint R)) := sorry

/-- A finite-type special fibre over a discrete valuation ring is Noetherian. -/
instance instIsNoetherianSpecialFiber
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [FiniteType f] :
    IsNoetherian (f.fiber (IsLocalRing.closedPoint R)) := sorry

/-- The irreducible components of a finite-type special fibre over a discrete valuation ring
form a finite type. -/
instance instFiniteSpecialFiberComponents
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [FiniteType f] :
    Finite (irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) := sorry

/-- The finitely supported vector of multiplicities of the irreducible components of the
special fibre. -/
noncomputable def specialFiberMultiplicities
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [FiniteType f] :
    irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i ↦
    (f.fiber (IsLocalRing.closedPoint R)).irreducibleComponentMultiplicity i

/-- Each entry of the special-fibre multiplicity vector is the multiplicity of that
irreducible component. -/
theorem specialFiberMultiplicities_apply
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [FiniteType f]
    (i : irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) :
    f.specialFiberMultiplicities i =
      (f.fiber (IsLocalRing.closedPoint R)).irreducibleComponentMultiplicity i := sorry

/-- Flatness over a discrete valuation ring makes the special fibre an effective Cartier
divisor. -/
instance instIsEffectiveCartierDivisorSpecialFiber
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Flat f] :
    IsEffectiveCartierDivisor (f.fiberι (IsLocalRing.closedPoint R)) := sorry

/-- The ideal-sheaf presentation of a flat special fibre is an effective Cartier divisor. -/
instance instIsEffectiveCartierDivisorSpecialFiberIdeal
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Flat f] :
    IsEffectiveCartierDivisor f.specialFiberIdeal.subschemeι := sorry

/-- On a regular finite-type flat model, every reduced irreducible component of the special
fibre is an effective Cartier divisor. -/
instance instIsEffectiveCartierDivisorSpecialFiberComponent
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [FiniteType f] [Scheme.Regular X]
    (i : irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) :
    IsEffectiveCartierDivisor (f.specialFiberComponent i).subschemeι := sorry

/-- The special fibre is the multiplicity-weighted sum of its reduced irreducible components. -/
theorem specialFiber_eq_weightedSum_of_regularModel
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [FiniteType f] [Scheme.Regular X] :
    f.specialFiberIdeal =
      IdealSheafData.effectiveCartierDivisorWeightedSum
        f.specialFiberMultiplicities f.specialFiberComponent := sorry

/-- The invertible sheaf associated to the special fibre of a flat model is isomorphic to the
structure sheaf. -/
theorem specialFiberAssociatedSheaf_isIsomorphic
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Flat f] :
    IsIsomorphic f.specialFiberIdeal.associatedSheaf
      (SheafOfModules.unit X.ringCatSheaf : X.Modules) := sorry

end AlgebraicGeometry.Scheme.Hom
