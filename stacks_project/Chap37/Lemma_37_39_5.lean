module

public import ReasLib.AlgebraicGeometry.Scheme.ArtinApproximation.FiniteTypeFactorization
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

/- Lemma 37.39.5: for a finite-type morphism of Noetherian schemes and a local
`𝒪_{S,s}`-algebra map `σ : 𝒪_{T,t} → Ô_{S,s}`, every positive order admits a pointed
finite-type morphism to `(T, t)` through which `σ` factors, and every other local
`𝒪_{S,s}`-algebra map factoring through the same stalk map agrees with `σ` modulo
`m_s ^ N`. -/
@[stacks 0CAX]
#check (AlgebraicGeometry.ArtinApproximation.exists_finiteTypeFactorization :
  ∀ {S T : Scheme.{u}} (f : T ⟶ S) [IsNoetherian S] [IsNoetherian T]
    [Scheme.Hom.FiniteType f] (s : S) (t : T) (ht : f t = s)
    (σ : T.presheaf.stalk t →+*
      AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))
    [IsLocalHom σ]
    (hσ_over : σ.comp (ht ▸ (f.stalkMap t).hom) =
      algebraMap (S.presheaf.stalk s)
        (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))
    (N : ℕ) (hN : 1 ≤ N),
    ∃ (T' : Scheme.{u}) (t' : T') (g : T' ⟶ T)
        (hfinite : Scheme.Hom.FiniteType g) (hgt : g t' = t)
        (τ : T'.presheaf.stalk t' →+*
          AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))
        (hτ : τ.comp (hgt ▸ (g.stalkMap t').hom) = σ),
      ∀ (σ' : T.presheaf.stalk t →+*
          AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))
          [IsLocalHom σ'],
        σ'.comp (ht ▸ (f.stalkMap t).hom) =
            algebraMap (S.presheaf.stalk s)
              (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
                (S.presheaf.stalk s)) →
          (∃ τ' : T'.presheaf.stalk t' →+*
              AdicCompletion (maximalIdeal (S.presheaf.stalk s))
                (S.presheaf.stalk s),
            τ'.comp (hgt ▸ (g.stalkMap t').hom) = σ') →
          ∀ a : T.presheaf.stalk t,
            σ a - σ' a ∈
              AdicCompletion.extendedIdealPow (maximalIdeal (S.presheaf.stalk s)) N)
