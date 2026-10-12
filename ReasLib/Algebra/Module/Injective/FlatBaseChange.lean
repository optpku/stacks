/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Injective.FlatLocal

@[expose] public section

open scoped TensorProduct TensorProduct.Right

universe u v w

/-- A flat base change satisfying the prime-localized contraction condition preserves
injectivity of modules over commutative Noetherian rings. -/
theorem Module.Injective.tensorProduct_of_flat_of_localized_comap_eq
    (A : Type u) (B : Type v) (I : Type w)
    [CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B] [Module.Flat A B]
    [AddCommGroup I] [Module A I] [Module.Injective A I]
    (hprime : ∀ q : PrimeSpectrum B,
      Ideal.map (algebraMap B (Localization.AtPrime q.asIdeal))
          (Ideal.map (algebraMap A B) (q.asIdeal.under A)) =
        Ideal.map (algebraMap B (Localization.AtPrime q.asIdeal)) q.asIdeal) :
    Module.Injective B (I ⊗[A] B) := sorry
