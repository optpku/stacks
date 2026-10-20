module

public import ReasLib.RingTheory.RingHom.Local.PlaneOriginChart
import StacksCheckRecall

/-!
# Exercise 111.56.4

An injective local homomorphism of local rings whose induced map on prime spectra is
not surjective.
-/

universe u

/- Exercise 111.56.4 (1): the displayed local homomorphism of local rings is injective. -/
@[stacks 09TZ]
#check (PlaneOriginChart.hom_injective :
  ∀ (k : Type u) [Field k], Function.Injective (PlaneOriginChart.hom k))

/- Exercise 111.56.4 (2): the induced map on prime spectra of this injective local
homomorphism of local rings is not surjective. -/
@[stacks 09TZ]
#check (PlaneOriginChart.hom_comap_not_surjective :
  ∀ (k : Type u) [Field k],
    ¬ Function.Surjective (PrimeSpectrum.comap (PlaneOriginChart.hom k)))
