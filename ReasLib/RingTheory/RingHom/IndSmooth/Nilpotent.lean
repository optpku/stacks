/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.RingHom.Flat
public import ReasLib.RingTheory.RingHom.IndSmooth.Basic
public import ReasLib.RingTheory.RingHom.Quotient

/-!
# Ind-smooth maps and nilpotent quotients

Ind-smoothness of a flat map can be tested after quotienting by a nilpotent
ideal in the source and its extension to the target.
-/

@[expose] public section

universe u v

namespace RingHom.IndSmooth

variable {R : Type u} {A : Type v}
variable [CommRing R] [CommRing A]

/-- Ind-smoothness of a flat ring homomorphism lifts across a nilpotent quotient of
the source and the corresponding quotient of the target. -/
@[stacks 07CM]
theorem of_quotient_nilpotent
    (f : R →+* A) (hf : f.Flat) (I : Ideal R) (hI : IsNilpotent I)
    (hquot : (f.quotientByIdeal I).IndSmooth) : f.IndSmooth := sorry

end RingHom.IndSmooth
