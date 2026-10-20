/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.ExteriorPower.Forms
public import ReasLib.RingTheory.AdicCompletion.PrincipalMaps

@[expose] public section

/-!
# Principal-adic completion of exterior forms

Complete the degree-indexed exterior-form family over its coefficient ring. The degree-zero
term is the completed ring, degree one is the completed module, and higher terms complete the
corresponding exterior powers. No derivation or divided-power structure is required.
-/

universe u

namespace exteriorPower

/-- The principal `p`-adic completion of the degree-`i` exterior forms of a module. -/
noncomputable abbrev completedForm (B : Type u) [CommRing B] (p : ℕ)
    (Ω : Type u) [AddCommGroup Ω] [Module B Ω] (i : ℕ) : Type u :=
  AdicCompletion (AdicCompletion.principalIdeal B p) (form B Ω i)

/-- Degree-zero completed forms are the completed coefficient ring. -/
@[simp]
theorem completedForm_zero (B : Type u) [CommRing B] (p : ℕ)
    (Ω : Type u) [AddCommGroup Ω] [Module B Ω] :
    completedForm B p Ω 0 = AdicCompletion (AdicCompletion.principalIdeal B p) B := rfl

/-- Degree-one completed forms are the completion of the original module. -/
@[simp]
theorem completedForm_one (B : Type u) [CommRing B] (p : ℕ)
    (Ω : Type u) [AddCommGroup Ω] [Module B Ω] :
    completedForm B p Ω 1 = AdicCompletion (AdicCompletion.principalIdeal B p) Ω := rfl

end exteriorPower
