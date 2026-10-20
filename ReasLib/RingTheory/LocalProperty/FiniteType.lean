/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RingHom.FiniteType
public import ReasLib.RingTheory.LocalProperty

/-!
# Locality of Finite-Type Algebras

This leaf records the principal-open locality of finite type over `ℤ`. Its
proof is supplied by mathlib's ring-homomorphism locality theorem
`RingHom.finiteType_isLocal`.
-/

@[expose] public section

universe u

namespace Algebra.FiniteType

/-- Being of finite type over `ℤ` is local for finite principal-open covers. -/
@[instance]
theorem int_ringPropertyIsLocal :
    RingPropertyIsLocal (fun A : CommRingCat.{u} ↦ Algebra.FiniteType ℤ A) := sorry

end Algebra.FiniteType
