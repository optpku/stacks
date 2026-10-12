/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.EulerCharacteristic
import StacksCheckRecall

universe u v

/- Lemma 42.2.4 (1): the multiplicity of a two-periodic complex of finite-length modules is
the length of its degree-zero term minus the length of its degree-one term. -/
@[stacks 0EA8] #check
  (CategoryTheory.CochainComplex.multiplicity_eq_length_sub_length :
    ∀ {R : Type u} [Ring R] (K : CochainComplex (ModuleCat.{v} R) (ZMod 2))
      (h₀ : IsFiniteLength R (K.X 0)) (h₁ : IsFiniteLength R (K.X 1)),
      CategoryTheory.CochainComplex.multiplicity K
          (CategoryTheory.CochainComplex.homology_isFiniteLength K 0 h₀)
          (CategoryTheory.CochainComplex.homology_isFiniteLength K 1 h₁) =
        ((Module.length R (K.X 0)).toNat : ℤ) - ((Module.length R (K.X 1)).toNat : ℤ))

/- Lemma 42.2.4 (2): the multiplicity of a two-periodic endomorphism on a finite-length
module is zero. -/
@[stacks 0EA8] #check
  (CategoryTheory.TwoPeriodicEndomorphism.multiplicity_eq_zero_of_isFiniteLength :
    ∀ {R : Type u} [Ring R]
      (K : CategoryTheory.TwoPeriodicEndomorphism (ModuleCat.{v} R))
      (hK : IsFiniteLength R K.X),
      K.multiplicity
          (CategoryTheory.TwoPeriodicEndomorphism.homology_isFiniteLength K hK 0)
          (CategoryTheory.TwoPeriodicEndomorphism.homology_isFiniteLength K hK 1) = 0)
