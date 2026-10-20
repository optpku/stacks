module

public import ReasLib.Algebra.Module.FinitePresentation.Noetherian
public import ReasLib.Algebra.Module.Injective.ResidueField
public import ReasLib.Algebra.Module.MatlisDuality.ArtinianCopresentation
import StacksCheckRecall

@[expose] public section

universe u v w

/- Lemma 47.7.7 (1): over a Noetherian local ring, the ascending chain condition,
finite generation, and the existence of a finite free presentation are equivalent. -/
@[stacks 08Z8]
#check (Module.noetherianFinitePresentation_tfae :
  ∀ (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M],
    List.TFAE
      [ IsNoetherian R M
      , Module.Finite R M
      , ∃ n m : ℕ, ∃ f : (Fin m → R) →ₗ[R] (Fin n → R),
          ∃ g : (Fin n → R) →ₗ[R] M, Function.Exact f g ∧ Function.Surjective g
      ])

/- Lemma 47.7.7 (2): over a Noetherian local ring, the descending chain condition
is equivalent both to maximal-ideal-power torsion with finite socle and to admitting
a finite copresentation by a chosen injective hull of the residue field. -/
@[stacks 08Z8]
#check (LinearMap.IsInjectiveHull.artinianModule_tfae :
  ∀ (R : Type u) (E : Type v) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup E] [Module R E] [Module.Injective R E]
    (ι : IsLocalRing.ResidueField R →ₗ[R] E) (hι : ι.IsInjectiveHull)
    (M : Type w) [AddCommGroup M] [Module R M],
    List.TFAE
      [ IsArtinian R M
      , Module.IsIdealPowerTorsion (IsLocalRing.maximalIdeal R) M ∧
          Module.Finite (IsLocalRing.ResidueField R)
            (Submodule.torsionBySet R M (IsLocalRing.maximalIdeal R))
      , ∃ n m : ℕ, ∃ f : M →ₗ[R] (Fin n → E),
          ∃ g : (Fin n → E) →ₗ[R] (Fin m → E),
            Function.Injective f ∧ Function.Exact f g
      ])
