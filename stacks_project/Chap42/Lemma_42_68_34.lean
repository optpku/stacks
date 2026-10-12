/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.ScalarQuotient.Determinant.ShortExact
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

/- Lemma 42.68.34: the scalar-quotient determinant of the middle term of a short
exact sequence of finite dimension-one modules is the product of those of the
outer terms when both scalars act regularly on all three modules. -/
@[stacks 02Q3] #check
  (CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientDeterminant_eq_mul_of_shortExact :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      (S : ShortComplex (ModuleCat.{v} A))
      [Module.Finite A S.X₁] [Module.Finite A S.X₂] [Module.Finite A S.X₃]
      (hS : S.ShortExact) (a b : A)
      (ha₁ : IsSMulRegular S.X₁ a) (hb₁ : IsSMulRegular S.X₁ b)
      (ha₂ : IsSMulRegular S.X₂ a) (hb₂ : IsSMulRegular S.X₂ b)
      (ha₃ : IsSMulRegular S.X₃ a) (hb₃ : IsSMulRegular S.X₃ b)
      (hdim₁ : Module.supportDim A S.X₁ = 1)
      (hdim₂ : Module.supportDim A S.X₂ = 1)
      (hdim₃ : Module.supportDim A S.X₃ = 1),
      CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientDeterminant
          S.X₂ a b ha₂ hb₂ hdim₂ =
        CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientDeterminant
            S.X₁ a b ha₁ hb₁ hdim₁ *
          CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientDeterminant
            S.X₃ a b ha₃ hb₃ hdim₃)
