/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Length

/-!
# Multiplicity of Two-Periodic Complexes

This file defines the integer-valued difference of the degree-zero and degree-one homology
lengths of a two-periodic complex and its specialization to a two-periodic endomorphism.
-/

@[expose] public section

universe u v

namespace CategoryTheory.CochainComplex

variable {R : Type u} [Ring R]

/-- The multiplicity of a two-periodic complex with finite-length homology is the length in
degree `0` minus the length in degree `1`. -/
noncomputable def multiplicity (K : CochainComplex (ModuleCat.{v} R) (ZMod 2))
    (h₀ : IsFiniteLength R (K.homology 0)) (h₁ : IsFiniteLength R (K.homology 1)) : ℤ :=
  ((Module.length R (K.homology 0)).toNat : ℤ) -
    ((Module.length R (K.homology 1)).toNat : ℤ)

/-- The defining homology-length formula for `CochainComplex.multiplicity`. -/
theorem multiplicity_def (K : CochainComplex (ModuleCat.{v} R) (ZMod 2))
    (h₀ : IsFiniteLength R (K.homology 0)) (h₁ : IsFiniteLength R (K.homology 1)) :
    multiplicity K h₀ h₁ =
      ((Module.length R (K.homology 0)).toNat : ℤ) -
        ((Module.length R (K.homology 1)).toNat : ℤ) := sorry

end CategoryTheory.CochainComplex

namespace CategoryTheory.TwoPeriodicEndomorphism

variable {R : Type u} [Ring R]

/-- The multiplicity, also called the additive Herbrand quotient, of a two-periodic
endomorphism with finite-length homology. -/
noncomputable def multiplicity (K : TwoPeriodicEndomorphism (ModuleCat.{v} R))
    (h₀ : IsFiniteLength R (K.toCochainComplex.homology 0))
    (h₁ : IsFiniteLength R (K.toCochainComplex.homology 1)) : ℤ :=
  CochainComplex.multiplicity K.toCochainComplex h₀ h₁

/-- The multiplicity of a two-periodic endomorphism is computed on its associated cochain
complex. -/
theorem multiplicity_eq (K : TwoPeriodicEndomorphism (ModuleCat.{v} R))
    (h₀ : IsFiniteLength R (K.toCochainComplex.homology 0))
    (h₁ : IsFiniteLength R (K.toCochainComplex.homology 1)) :
    K.multiplicity h₀ h₁ = CochainComplex.multiplicity K.toCochainComplex h₀ h₁ := sorry

/-- The multiplicity of a two-periodic endomorphism is the difference of the lengths of its
kernel/image quotient modules. -/
theorem multiplicity_eq_quotientLengths (K : TwoPeriodicEndomorphism (ModuleCat.{v} R))
    (h₀ : IsFiniteLength R (K.toCochainComplex.homology 0))
    (h₁ : IsFiniteLength R (K.toCochainComplex.homology 1)) :
    K.multiplicity h₀ h₁ =
      ((Module.length R (K.d₀.hom.ker ⧸ K.d₁.hom.range.submoduleOf K.d₀.hom.ker)).toNat : ℤ) -
        ((Module.length R (K.d₁.hom.ker ⧸ K.d₀.hom.range.submoduleOf K.d₁.hom.ker)).toNat : ℤ) := sorry

end CategoryTheory.TwoPeriodicEndomorphism
