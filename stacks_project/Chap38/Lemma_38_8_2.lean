module

public import ReasLib.RingTheory.AdicCompletion.MittagLeffler
import StacksCheckRecall

@[expose] public section

universe u v

/- Lemma 38.8.2 (1): the adic completion is flat. -/
@[stacks 05DK] #check
  (@Module.Flat.adicCompletion :
    ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
      (I : Ideal R) [IsNoetherianRing R] [IsAdicComplete I R] [Module.Flat R M]
      [Module.Projective (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))],
      Module.Flat R (AdicCompletion I M))

/- Lemma 38.8.2 (2): the adic completion is Mittag-Leffler. -/
@[stacks 05DK] #check
  (@Module.MittagLeffler.adicCompletion :
    ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
      (I : Ideal R) [IsNoetherianRing R] [IsAdicComplete I R] [Module.Flat R M]
      [Module.Projective (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))],
      Module.MittagLeffler R (AdicCompletion I M))
