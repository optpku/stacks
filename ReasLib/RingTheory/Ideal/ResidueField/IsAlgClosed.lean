/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section

universe u v

namespace Ideal.ResidueField

/-- A nonzero prime residue field is algebraically closed when the base is integrally
closed in a separably closed fraction-field model. -/
theorem isAlgClosed_of_isSepClosed_fractionRing
    (A : Type u) [CommRing A] [IsDomain A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsIntegrallyClosedIn A K] [IsSepClosed K]
    (p : Ideal A) [p.IsPrime] (hp : p ≠ ⊥) :
    IsAlgClosed p.ResidueField := sorry

/-- The residue field at a nonzero prime ideal of a domain with integrally closed
base and separably closed fraction ring is algebraically closed. -/
instance instIsAlgClosed
    {A : Type u} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [IsSepClosed (FractionRing A)] (p : Ideal A) [p.IsPrime] [NeZero p] :
    IsAlgClosed p.ResidueField := sorry

end Ideal.ResidueField
