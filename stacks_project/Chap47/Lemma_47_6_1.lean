module

public import ReasLib.Algebra.Module.Injective.Hull.Length
import StacksCheckRecall

@[expose] public section

universe u v w

/- Lemma 47.6.1 (1): For a finite module over an Artinian local ring, its length
equals the length of its module of linear maps into an injective hull of the residue
field. -/
@[stacks 08YX] #check
  (Module.length_linearMap_to_injectiveHull :
    ∀ (R : Type u) (E : Type v) (M : Type w) [CommRing R] [IsLocalRing R]
      [IsArtinianRing R] [AddCommGroup E] [Module R E] [Module.Injective R E]
      [AddCommGroup M] [Module R M] [Module.Finite R M]
      (ι : IsLocalRing.ResidueField R →ₗ[R] E) (hι : ι.IsInjectiveHull),
      Module.length R M = Module.length R (M →ₗ[R] E))

/- Lemma 47.6.1 (2): An injective hull of the residue field of an Artinian local
ring is finite as a module. -/
@[stacks 08YX] #check
  (Module.Finite.of_injectiveHull :
    ∀ (R : Type u) (E : Type v) [CommRing R] [IsLocalRing R] [IsArtinianRing R]
      [AddCommGroup E] [Module R E] [Module.Injective R E]
      (ι : IsLocalRing.ResidueField R →ₗ[R] E) (hι : ι.IsInjectiveHull),
      Module.Finite R E)
