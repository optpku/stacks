module

public import ReasLib.Algebra.Module.Injective.FlatBaseChange
import StacksCheckRecall

@[expose] public section

open scoped TensorProduct TensorProduct.Right

universe u v w

/- Lemma 47.26.4: Let `A → B` be a flat homomorphism of Noetherian rings such that,
for every `q : PrimeSpectrum B`, the extension to `Localization.AtPrime q.asIdeal` of the
contraction of `q.asIdeal` is the extension of `q.asIdeal`. If `I` is an injective `A`-module,
then `I ⊗[A] B` is an injective `B`-module. -/
@[stacks 0E4F] #check
  (Module.Injective.tensorProduct_of_flat_of_localized_comap_eq :
    ∀ (A : Type u) (B : Type v) (I : Type w)
      [CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B]
      [Algebra A B] [Module.Flat A B]
      [AddCommGroup I] [Module A I] [Module.Injective A I]
      (hprime : ∀ q : PrimeSpectrum B,
        Ideal.map (algebraMap B (Localization.AtPrime q.asIdeal))
            (Ideal.map (algebraMap A B) (q.asIdeal.under A)) =
          Ideal.map (algebraMap B (Localization.AtPrime q.asIdeal)) q.asIdeal),
      Module.Injective B (I ⊗[A] B))
