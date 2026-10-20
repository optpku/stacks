module

public import ReasLib.Algebra.Module.MatlisDuality.InjectiveHullArtinian
import StacksCheckRecall

@[expose] public section

universe u v

/- Lemma 47.7.6: An injective hull of the residue field of a Noetherian local ring
satisfies the descending chain condition on its submodules. -/
@[stacks 08Z7] #check
  (LinearMap.IsInjectiveHull.isArtinian :
    ∀ (R : Type u) (E : Type v) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
      [AddCommGroup E] [Module R E] [Module.Injective R E]
      {ι : IsLocalRing.ResidueField R →ₗ[R] E}, ι.IsInjectiveHull → IsArtinian R E)
