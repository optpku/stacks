/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Determinant
public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.ModuleEnd
public import ReasLib.Algebra.Category.ModuleCat.DualNumber.Residue

/-!
# Two-periodic complexes over the dual numbers

This file constructs the acyclic two-periodic complex on the regular dual-number
module with differentials given by unit multiples of `ε` and evaluates its determinant.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped DualNumber

universe u

namespace CategoryTheory.TwoPeriodicEndomorphism.DualNumber

variable {k : Type u} [Field k]

/-- Multiplication by the unit-scaled square-zero element `aε` on the regular
dual-number module. -/
def endomorphism (a : kˣ) : Module.End k[ε] k[ε] :=
  LinearMap.lsmul k[ε] k[ε] ((algebraMap k k[ε] (a : k)) * ε)

/-- The endomorphism `endomorphism a` acts by multiplication by `aε`. -/
@[simp]
theorem endomorphism_apply (a : kˣ) (x : k[ε]) :
    endomorphism a x = ((algebraMap k k[ε] (a : k)) * ε) * x := sorry

/-- The range of multiplication by `aε` is the ideal `(ε)`. -/
theorem endomorphism_range (a : kˣ) :
    (endomorphism a).range = _root_.DualNumber.epsIdeal k := sorry

/-- The kernel of multiplication by `aε` is the ideal `(ε)`. -/
theorem endomorphism_ker (a : kˣ) :
    (endomorphism a).ker = _root_.DualNumber.epsIdeal k := sorry

/-- The image of multiplication by `aε` lies in the kernel of multiplication by `bε`. -/
theorem range_le_ker (a b : kˣ) :
    (endomorphism a).range ≤ (endomorphism b).ker := sorry

/-- The two-periodic complex on the regular dual-number module whose differentials are
multiplication by `uε` and `vε`. -/
def complex (u v : kˣ) : TwoPeriodicEndomorphism (ModuleCat k[ε]) :=
  ofModuleEnd (endomorphism u) (endomorphism v)
    (range_le_ker u v) (range_le_ker v u)

/-- The carrier of the unit-scaled dual-number complex is the regular module. -/
@[simp]
theorem complex_X (u v : kˣ) :
    (complex u v).X = ModuleCat.of k[ε] k[ε] := sorry

/-- The degree-zero differential of the unit-scaled dual-number complex is multiplication
by `uε`. -/
@[simp]
theorem complex_d₀ (u v : kˣ) :
    (complex u v).d₀ = ModuleCat.ofHom (endomorphism u) := sorry

/-- The degree-one differential of the unit-scaled dual-number complex is multiplication
by `vε`. -/
@[simp]
theorem complex_d₁ (u v : kˣ) :
    (complex u v).d₁ = ModuleCat.ofHom (endomorphism v) := sorry

/-- The regular module over the dual numbers has finite length. -/
theorem regular_isFiniteLength : IsFiniteLength k[ε] k[ε] := sorry

/-- The unit-scaled dual-number complex is acyclic. -/
theorem complex_acyclic (u v : kˣ) :
    (complex u v).toCochainComplex.Acyclic := sorry

/-- The periodic determinant of the regular dual-number module with differentials given by
multiplication by `uε` and `vε` is the residue of `-u / v`. -/
theorem determinant_eq_neg_div (u v : kˣ) :
    determinant (complex u v) regular_isFiniteLength (complex_acyclic u v) =
      Units.map
        ((IsLocalRing.residue k[ε]).comp (algebraMap k k[ε])).toMonoidHom (-u / v) := sorry

end CategoryTheory.TwoPeriodicEndomorphism.DualNumber
