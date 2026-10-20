/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Module

/-!
# Support of the annihilator quotient

The quotient by the module annihilator is the canonical faithful scalar
realization.  Its full-support statement is packaged here so applications do
not have to rebuild the quotient module and scalar-tower instances.
-/

@[expose] public section

universe u v

namespace Module

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- The canonical quotient by `Ann_R(M)` gives `M` full support. -/
theorem support_quotientAnnihilator_eq_univ :
    let A := R ⧸ Module.annihilator R M
    letI : Module A M := Module.quotientAnnihilator
    letI : IsScalarTower R A M :=
      Module.IsTorsionBySet.isScalarTower (Module.isTorsionBySet_annihilator R M)
    Module.support A M = Set.univ := sorry

end Module
