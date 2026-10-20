module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.RingTheory.AdicCompletion.Congruence

@[expose] public section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry.ArtinApproximation

/-- A local algebra map from the stalk of a finite-type morphism of Noetherian schemes to a
completed local ring factors through a pointed finite-type refinement that determines the map to
any prescribed positive order. -/
theorem exists_finiteTypeFactorization
    {S T : Scheme.{u}} (f : T ⟶ S) [IsNoetherian S] [IsNoetherian T]
    [Scheme.Hom.FiniteType f] (s : S) (t : T) (ht : f t = s)
    (σ : T.presheaf.stalk t →+*
      AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))
    [IsLocalHom σ]
    (hσ_over : σ.comp (ht ▸ (f.stalkMap t).hom) =
      algebraMap (S.presheaf.stalk s)
        (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))
    (N : ℕ) (hN : 1 ≤ N) :
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
              AdicCompletion.extendedIdealPow (maximalIdeal (S.presheaf.stalk s)) N := sorry

end AlgebraicGeometry.ArtinApproximation
