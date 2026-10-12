/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Nilpotent Perturbations of Module Endomorphisms

This leaf records the module-theoretic core of the fact that an endomorphism
which is the identity modulo a nilpotent ideal is invertible.  It is stated in
terms of the range of the error endomorphism, so it applies independently of
how the module or its generators are presented.

@stack 07RD
-/

@[expose] public section

universe u v

namespace Module.End

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Tag `07RD`: an endomorphism whose image is contained in the scalar span of
a nilpotent ideal is nilpotent. -/
@[stacks 07RD "nilpotent module-endomorphism error"]
theorem isNilpotent_of_range_le_smul_top
    (d : Module.End R M) {I : Ideal R} (hI : IsNilpotent I)
    (hd : LinearMap.range d ≤ I • (⊤ : Submodule R M)) :
    IsNilpotent d := sorry

/-- Tag `07RD`: an endomorphism congruent to the identity modulo the scalar
span of a nilpotent ideal is a unit in `Module.End R M`. -/
@[stacks 07RD "unit module-endomorphism modulo a nilpotent ideal"]
theorem isUnit_of_sub_one_range_le_smul_top
    (f : Module.End R M) {I : Ideal R} (hI : IsNilpotent I)
    (hf : LinearMap.range (f - 1) ≤ I • (⊤ : Submodule R M)) :
    IsUnit f := sorry

end Module.End
