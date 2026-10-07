module

public import ReasLib.Algebra.Category.ModuleCat.Tor.Factorisation
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 51.20.1: if a map from a finitely presented module induces the zero map on
`Tor₁` against every module, then it factors through a free module. -/
@[stacks 0G9T] #check
  (@LinearMap.exists_free_factorisation_of_torOne_map_eq_zero :
    {R M M' : Type u} → [CommRing R] → [AddCommGroup M] → [Module R M] →
      [AddCommGroup M'] → [Module R M'] → [Module.FinitePresentation R M] →
      (f : M →ₗ[R] M') →
      (∀ N : ModuleCat.{u} R,
        ((CategoryTheory.Tor (ModuleCat.{u} R) 1).map (ModuleCat.ofHom f)).app N = 0) →
      ∃ (ι : Type u) (toFree : M →ₗ[R] (ι →₀ R))
        (fromFree : (ι →₀ R) →ₗ[R] M'),
        fromFree.comp toFree = f)
