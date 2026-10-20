/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Multiplicity

/-!
# Euler Characteristic of Two-Periodic Complexes

This file relates the multiplicity of a two-periodic complex of finite-length modules to the
difference of the lengths of its terms.
-/

@[expose] public section

universe u v

namespace CategoryTheory.CochainComplex

variable {R : Type u} [Ring R]

/-- The homology of a two-periodic complex is of finite length whenever its term in that
degree is of finite length. -/
theorem homology_isFiniteLength (K : CochainComplex (ModuleCat.{v} R) (ZMod 2))
    (i : ZMod 2) (h : IsFiniteLength R (K.X i)) : IsFiniteLength R (K.homology i) := sorry

/-- The multiplicity of a two-periodic complex of finite-length modules is the difference
of the lengths of its degree-zero and degree-one terms. -/
theorem multiplicity_eq_length_sub_length (K : CochainComplex (ModuleCat.{v} R) (ZMod 2))
    (h₀ : IsFiniteLength R (K.X 0)) (h₁ : IsFiniteLength R (K.X 1)) :
    multiplicity K (homology_isFiniteLength K 0 h₀) (homology_isFiniteLength K 1 h₁) =
      ((Module.length R (K.X 0)).toNat : ℤ) - ((Module.length R (K.X 1)).toNat : ℤ) := sorry

end CategoryTheory.CochainComplex

namespace CategoryTheory.TwoPeriodicEndomorphism

variable {R : Type u} [Ring R]

/-- The homology in every degree of a two-periodic endomorphism on a finite-length module
is of finite length. -/
theorem homology_isFiniteLength (K : TwoPeriodicEndomorphism (ModuleCat.{v} R))
    (hK : IsFiniteLength R K.X) (i : ZMod 2) :
    IsFiniteLength R (K.toCochainComplex.homology i) := sorry

/-- The multiplicity of a two-periodic endomorphism on a finite-length module is zero. -/
theorem multiplicity_eq_zero_of_isFiniteLength
    (K : TwoPeriodicEndomorphism (ModuleCat.{v} R)) (hK : IsFiniteLength R K.X) :
    K.multiplicity (K.homology_isFiniteLength hK 0) (K.homology_isFiniteLength hK 1) = 0 := sorry

end CategoryTheory.TwoPeriodicEndomorphism
