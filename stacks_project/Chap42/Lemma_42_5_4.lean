module

public import ReasLib.RingTheory.LocalRing.TameSymbol.Factorization.BaseChange
import StacksCheckRecall

@[expose] public section

open IsLocalRing

universe u v w x

/- Lemma 42.5.4: under a flat local homomorphism of one-dimensional Noetherian local rings,
the `m`-th power of a source tame-symbol value maps to every target tame-symbol value, where
`m` is the length of the quotient by the extended maximal ideal. -/
@[stacks 0EPG]
#check (TameSymbol.Factorization.map_value_pow_eq :
    ∀ {A : Type u} {A' : Type v} {B : Type w} {B' : Type x}
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing A'] [IsLocalRing A'] [IsNoetherianRing A']
    [Algebra A A'] [IsLocalHom (algebraMap A A')] [Module.Flat A A']
    [CommRing B] [Algebra A B] [Module.Finite A B]
    [CommRing B'] [Algebra A' B'] [Module.Finite A' B']
    (hdimA : ringKrullDim A = 1) (hdimA' : ringKrullDim A' = 1)
    (a₁ a₂ : A) (ha₁ : a₁ ∈ nonZeroDivisors A) (ha₂ : a₂ ∈ nonZeroDivisors A)
    (D : TameSymbol.Factorization A B a₁ a₂)
    (D' : TameSymbol.Factorization A' B'
      (algebraMap A A' a₁) (algebraMap A A' a₂)),
    Units.map (Ideal.ResidueField.map (maximalIdeal A) (maximalIdeal A')
      (algebraMap A A') (IsLocalRing.maximalIdeal_comap (algebraMap A A')).symm).toMonoidHom
        (D.value ^ (Module.length A'
          (A' ⧸ (maximalIdeal A).map (algebraMap A A'))).toNat) =
      D'.value)
