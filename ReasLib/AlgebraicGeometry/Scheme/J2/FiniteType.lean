/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.J2.Locality
public import ReasLib.RingTheory.Regular.JRing.CompleteLocal
public import ReasLib.RingTheory.Regular.JRing.Dedekind
public import ReasLib.RingTheory.Regular.JRing.DimensionOne
public import ReasLib.RingTheory.Regular.JRing.EssentialFiniteness
public import ReasLib.RingTheory.Regular.JRing.Field

/-!
# J-2 schemes locally of finite type

Schemes locally of finite type over standard affine J-2 bases are J-2.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- The spectrum of a J-2 ring is a J-2 scheme. -/
instance instIsJ2Spec (R : Type u) [CommRing R] [IsJ2Ring.{u, u} R] :
    IsJ2 (Spec (CommRingCat.of R)) where
  toIsLocallyNoetherian := inferInstance
  regularLocus_isOpen_of_locallyOfFiniteType := by
    intro Y f
    sorry

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.LocallyOfFiniteType

/-- A scheme locally of finite type over the spectrum of a J-2 ring is J-2. -/
theorem isJ2_over_spec (R : Type u) [CommRing R] [IsJ2Ring.{u, u} R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] :
    Scheme.IsJ2 X :=
  Scheme.isJ2_of_locallyOfFiniteType f

/-- A scheme locally of finite type over a field is J-2. -/
theorem isJ2_over_field
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] :
    Scheme.IsJ2 X :=
  isJ2_over_spec k f

/-- A scheme locally of finite type over a Noetherian complete local ring is J-2. -/
theorem isJ2_over_noetherianCompleteLocalRing
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] :
    Scheme.IsJ2 X :=
  isJ2_over_spec R f

/-- A scheme locally of finite type over the spectrum of the integers is J-2. -/
theorem isJ2_over_integers
    {X : Scheme} (f : X ⟶ Spec (CommRingCat.of ℤ)) [LocallyOfFiniteType f] :
    Scheme.IsJ2 X :=
  isJ2_over_spec ℤ f

/-- A scheme locally of finite type over a Noetherian local ring of Krull dimension one is
J-2. -/
theorem isJ2_over_noetherianLocalRing_of_ringKrullDim_eq_one
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (h_dimension : ringKrullDim R = 1)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] :
    Scheme.IsJ2 X :=
  @isJ2_over_spec R _ (IsJ2Ring.of_localRing_dimensionOne R h_dimension) X f _

/-- A scheme locally of finite type over a Nagata ring of Krull dimension one is J-2. -/
theorem isJ2_over_nagataRing_of_ringKrullDim_eq_one
    {R : Type u} [CommRing R] [NagataRing R] (h_dimension : ringKrullDim R = 1)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] :
    Scheme.IsJ2 X :=
  @isJ2_over_spec R _ (IsJ2Ring.of_nagataRing_dimensionOne R h_dimension) X f _

/-- A scheme locally of finite type over a Dedekind domain whose fraction field has
characteristic zero is J-2. -/
theorem isJ2_over_dedekindDomain_of_fractionRing_charZero
    {R : Type u} [CommRing R] [IsDedekindDomain R] [CharZero (FractionRing R)]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] :
    Scheme.IsJ2 X :=
  isJ2_over_spec R f

end AlgebraicGeometry.LocallyOfFiniteType
