/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Torsion.Basic

import Mathlib.Tactic.CrossRefAttribute

/-!
# Functoriality of torsion by an element

A ring homomorphism carries elements killed by `a` to elements killed by `a` after restriction of
scalars.  This file owns the resulting linear map between the two torsion submodules.

@stack 0BNT
-/

@[expose] public section

noncomputable section

universe u v

namespace Submodule

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S]

/-- A ring homomorphism sends an element killed by `a` to an element killed by `a`. -/
@[stacks 0BNT "torsion by an element is functorial"]
theorem algebraMap_mem_torsionBy
    (φ : R →+* S) (a : R) (x : torsionBy R R a) :
    let _ : Algebra R S := φ.toAlgebra
    (Algebra.linearMap R S) (x : R) ∈ torsionBy R S a := sorry

/-- The linear map on `a`-torsion induced by a ring homomorphism. -/
@[stacks 0BNT "the map on finite torsion stages"]
noncomputable def torsionByMap (φ : R →+* S) (a : R) :
    let _ : Algebra R S := φ.toAlgebra
    torsionBy R R a →ₗ[R] torsionBy R S a :=
  let _ : Algebra R S := φ.toAlgebra
  ((Algebra.linearMap R S).domRestrict (torsionBy R R a)).codRestrict
    (torsionBy R S a) (algebraMap_mem_torsionBy φ a)

/-- The map on torsion submodules is induced by the original ring homomorphism. -/
@[simp, stacks 0BNT "the map on finite torsion stages, on elements"]
theorem torsionByMap_apply (φ : R →+* S) (a : R) (x : torsionBy R R a) :
    let _ : Algebra R S := φ.toAlgebra
    ((torsionByMap φ a) x : S) = φ (x : R) := sorry

end Submodule
