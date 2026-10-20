/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Ideals modulo the action of the maximal ideal

For an ideal `I` of a local ring `R`, the quotient `I ⧸ m_R I` is a vector space
over the residue field of `R`.
-/

@[expose] public section

universe u

namespace IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- The quotient module `I ⧸ m_R I` of an ideal by the action of the maximal ideal. -/
def idealSmulQuot (I : Ideal R) : Type u :=
  I ⧸ (maximalIdeal R • ⊤ : Submodule R I)
deriving AddCommGroup, Module R, Module (R ⧸ maximalIdeal R)

namespace idealSmulQuot

/-- The quotient class of an element of `I` in `I ⧸ m_R I`. -/
def mk {I : Ideal R} : I → idealSmulQuot I :=
  Submodule.Quotient.mk

/-- The class of `x` vanishes if and only if the underlying element of `R` lies in `m_R * I`. -/
theorem mk_eq_zero_iff {I : Ideal R} (x : I) :
    mk x = 0 ↔ (x : R) ∈ maximalIdeal R * I :=
  sorry

/-- `I ⧸ m_R I` is a vector space over the residue field. -/
instance moduleResidueField {I : Ideal R} : Module (ResidueField R) (idealSmulQuot I) :=
  inferInstanceAs <| Module (R ⧸ maximalIdeal R) (I ⧸ (maximalIdeal R • ⊤ : Submodule R I))

end idealSmulQuot

end IsLocalRing
