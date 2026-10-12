/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.LocalRing.TameSymbol.Factorization.Independence
public import ReasLib.RingTheory.Norm.FiniteLengthBaseChange

@[expose] public section

open IsLocalRing

universe u v w x

namespace TameSymbol.Factorization

/-- Under a flat local map of one-dimensional Noetherian local rings, the image of a
factorization tame-symbol value raised to the closed-fiber length is the corresponding
factorization tame-symbol value after base change. -/
@[stacks 0EPG]
theorem map_value_pow_eq
    {A : Type u} {A' : Type v} {B : Type w} {B' : Type x}
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing A'] [IsLocalRing A'] [IsNoetherianRing A']
    [Algebra A A'] [IsLocalHom (algebraMap A A')] [Module.Flat A A']
    [CommRing B] [Algebra A B] [Module.Finite A B]
    [CommRing B'] [Algebra A' B'] [Module.Finite A' B']
    (hdimA : ringKrullDim A = 1) (hdimA' : ringKrullDim A' = 1)
    (a₁ a₂ : A) (ha₁ : a₁ ∈ nonZeroDivisors A) (ha₂ : a₂ ∈ nonZeroDivisors A)
    (D : Factorization A B a₁ a₂)
    (D' : Factorization A' B' (algebraMap A A' a₁) (algebraMap A A' a₂)) :
    Units.map (Ideal.ResidueField.map (maximalIdeal A) (maximalIdeal A')
      (algebraMap A A') (IsLocalRing.maximalIdeal_comap (algebraMap A A')).symm).toMonoidHom
        (D.value ^ (Module.length A'
          (A' ⧸ (maximalIdeal A).map (algebraMap A A'))).toNat) =
      D'.value := sorry

end TameSymbol.Factorization
