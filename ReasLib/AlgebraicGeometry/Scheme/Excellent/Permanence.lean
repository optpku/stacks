/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Excellent
public import ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- Quasi-excellence implies the Nagata property. -/
theorem nagata_of_quasiExcellent (X : Scheme.{u}) [QuasiExcellent X] :
    Nagata X := sorry

/-- Local finite type preserves quasi-excellence. -/
theorem quasiExcellent_of_locallyOfFiniteType {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiExcellent S] [LocallyOfFiniteType f] : QuasiExcellent X := sorry

/-- Local finite type preserves excellence. -/
theorem excellent_of_locallyOfFiniteType {X S : Scheme.{u}} (f : X ⟶ S)
    [Excellent S] [LocallyOfFiniteType f] : Excellent X := sorry

/-- Schemes locally of finite type over a field are excellent. -/
theorem excellent_of_locallyOfFiniteType_field {X : Scheme.{u}}
    (k : Type u) [Field k] (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] : Excellent X := sorry

/-- Schemes locally of finite type over a Noetherian complete local ring are excellent. -/
theorem excellent_of_locallyOfFiniteType_completeLocal {X : Scheme.{u}}
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] : Excellent X := sorry

/-- Schemes locally of finite type over the integers are excellent. -/
theorem excellent_of_locallyOfFiniteType_int {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of (ULift.{u} ℤ))) [LocallyOfFiniteType f] :
    Excellent X := sorry

/-- Schemes locally of finite type over a characteristic-zero Dedekind domain are excellent. -/
theorem excellent_of_locallyOfFiniteType_dedekindCharZero {X : Scheme.{u}}
    (R : Type u) [CommRing R] [IsDedekindDomain R] [CharZero R]
    (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] : Excellent X := sorry

end AlgebraicGeometry.Scheme
