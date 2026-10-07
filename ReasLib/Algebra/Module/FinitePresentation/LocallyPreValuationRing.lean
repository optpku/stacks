module

public import ReasLib.Algebra.Module.FinitePresentation.PreValuationRing
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite presentations over locally generalized valuation rings

This leaf records the local-to-global cyclic-retract theorem for finitely
presented modules.  The finite family and both splitting maps remain under the
source's existential quantifiers; no decomposition is chosen globally.

@stack 0ASQ
-/

@[expose] public section

open scoped DirectSum

universe u v

namespace Module.FinitePresentation

/-- Lemma 15.125.4 (0ASQ): if every maximal-ideal localization of `R` is a
generalized valuation ring, then every finitely presented `R`-module is a
retract of a finite direct sum of principal cyclic quotients. -/
@[stacks 0ASQ "finite cyclic retract over a locally generalized valuation ring"]
theorem existsRetractDirectSumPrincipalQuotients_of_localizedPreValuationRing
    {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]
    (hR : ∀ (m : Ideal R) [m.IsMaximal],
      PreValuationRing (Localization.AtPrime m)) :
    ∃ (n : ℕ) (f : Fin n → R)
      (i : M →ₗ[R] (⨁ j : Fin n, R ⧸ principalIdeal (f j)))
      (r : (⨁ j : Fin n, R ⧸ principalIdeal (f j)) →ₗ[R] M),
      r.comp i = LinearMap.id := sorry
-- Proof strategy: apply the 0ASM lifting criterion.  Localize a
-- principal-pure short exact sequence at each maximal ideal; principal purity
-- and short exactness localize, and the 0ASP decomposition over the resulting
-- pre-valuation ring gives local surjectivity on `Hom`.  Detect global
-- surjectivity at maximal localizations, obtain a retract of a direct sum of
-- principal quotients, and use finite presentation of `M` to shrink the
-- splitting maps to a finite support.

end Module.FinitePresentation
