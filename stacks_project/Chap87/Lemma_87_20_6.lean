module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Lemma_87_10_3_Types

/-!
# Lemma 87.20.6

On a formal algebraic space, the listed affine types are étale-local: they
hold for every affine étale chart if and only if they hold for some atlas as
in Definition 87.11.1.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry

/-- Lemma 87.20.6 (1): Let `S` be a scheme. Let `X` be a formal algebraic space
over `S`. The following are equivalent: every affine formal algebraic space
`Y` with a morphism `f : Y ⟶ X` that is representable by algebraic spaces and
étale is countably indexed; some `{X_ i ⟶ X}` as in Definition 87.11.1 has
each `X_ i` countably indexed. -/
@[stacks 0AKX]
theorem IsCountablyIndexedAffine.iff_etale_affine_atlas
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    (∀ {Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : Y ⟶ X),
        IsAffineFormalAlgebraicSpace Y → representableByAlgebraicSpaces f →
          relativelyEtale f → IsCountablyIndexedAffine Y) ↔
      ∃ (ι : Type (max u v))
        (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
        (π : ∀ i, X_ i ⟶ X) (c : Cofan X_) (hc : IsColimit c),
          (∀ i, IsAffineFormalAlgebraicSpace (X_ i)) ∧
            (∀ i, representableByAlgebraicSpaces (π i)) ∧
              (∀ i, relativelyEtale (π i)) ∧
                Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π) ∧
                  ∀ i, IsCountablyIndexedAffine (X_ i) :=
  sorry

/-- Lemma 87.20.6 (2): Let `S` be a scheme. Let `X` be a formal algebraic space
over `S`. The following are equivalent: every affine formal algebraic space
`Y` with a morphism `f : Y ⟶ X` that is representable by algebraic spaces and
étale is countably indexed and classical; some `{X_ i ⟶ X}` as in
Definition 87.11.1 has each `X_ i` countably indexed and classical. -/
@[stacks 0AKX]
theorem IsClassicalAffine.iff_etale_affine_atlas
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    (∀ {Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : Y ⟶ X),
        IsAffineFormalAlgebraicSpace Y → representableByAlgebraicSpaces f →
          relativelyEtale f →
            IsCountablyIndexedAffine Y ∧ IsClassicalAffine Y) ↔
      ∃ (ι : Type (max u v))
        (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
        (π : ∀ i, X_ i ⟶ X) (c : Cofan X_) (hc : IsColimit c),
          (∀ i, IsAffineFormalAlgebraicSpace (X_ i)) ∧
            (∀ i, representableByAlgebraicSpaces (π i)) ∧
              (∀ i, relativelyEtale (π i)) ∧
                Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π) ∧
                  ∀ i, IsCountablyIndexedAffine (X_ i) ∧ IsClassicalAffine (X_ i) :=
  sorry

/-- Lemma 87.20.6 (3): Let `S` be a scheme. Let `X` be a formal algebraic space
over `S`. The following are equivalent: every affine formal algebraic space
`Y` with a morphism `f : Y ⟶ X` that is representable by algebraic spaces and
étale is weakly adic; some `{X_ i ⟶ X}` as in Definition 87.11.1 has each
`X_ i` weakly adic. -/
@[stacks 0AKX]
theorem IsWeaklyAdicAffine.iff_etale_affine_atlas
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    (∀ {Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : Y ⟶ X),
        IsAffineFormalAlgebraicSpace Y → representableByAlgebraicSpaces f →
          relativelyEtale f → IsWeaklyAdicAffine Y) ↔
      ∃ (ι : Type (max u v))
        (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
        (π : ∀ i, X_ i ⟶ X) (c : Cofan X_) (hc : IsColimit c),
          (∀ i, IsAffineFormalAlgebraicSpace (X_ i)) ∧
            (∀ i, representableByAlgebraicSpaces (π i)) ∧
              (∀ i, relativelyEtale (π i)) ∧
                Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π) ∧
                  ∀ i, IsWeaklyAdicAffine (X_ i) :=
  sorry

/-- Lemma 87.20.6 (4): Let `S` be a scheme. Let `X` be a formal algebraic space
over `S`. The following are equivalent: every affine formal algebraic space
`Y` with a morphism `f : Y ⟶ X` that is representable by algebraic spaces and
étale is adic*; some `{X_ i ⟶ X}` as in Definition 87.11.1 has each `X_ i`
adic*. -/
@[stacks 0AKX]
theorem IsAdicStar.iff_etale_affine_atlas
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    (∀ {Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : Y ⟶ X),
        IsAffineFormalAlgebraicSpace Y → representableByAlgebraicSpaces f →
          relativelyEtale f → IsAdicStar Y) ↔
      ∃ (ι : Type (max u v))
        (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
        (π : ∀ i, X_ i ⟶ X) (c : Cofan X_) (hc : IsColimit c),
          (∀ i, IsAffineFormalAlgebraicSpace (X_ i)) ∧
            (∀ i, representableByAlgebraicSpaces (π i)) ∧
              (∀ i, relativelyEtale (π i)) ∧
                Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π) ∧
                  ∀ i, IsAdicStar (X_ i) :=
  sorry

/-- Lemma 87.20.6 (5): Let `S` be a scheme. Let `X` be a formal algebraic space
over `S`. The following are equivalent: every affine formal algebraic space
`Y` with a morphism `f : Y ⟶ X` that is representable by algebraic spaces and
étale is Noetherian; some `{X_ i ⟶ X}` as in Definition 87.11.1 has each
`X_ i` Noetherian. -/
@[stacks 0AKX]
theorem IsNoetherianAffine.iff_etale_affine_atlas
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    (∀ {Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : Y ⟶ X),
        IsAffineFormalAlgebraicSpace Y → representableByAlgebraicSpaces f →
          relativelyEtale f → IsNoetherianAffine Y) ↔
      ∃ (ι : Type (max u v))
        (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
        (π : ∀ i, X_ i ⟶ X) (c : Cofan X_) (hc : IsColimit c),
          (∀ i, IsAffineFormalAlgebraicSpace (X_ i)) ∧
            (∀ i, representableByAlgebraicSpaces (π i)) ∧
              (∀ i, relativelyEtale (π i)) ∧
                Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π) ∧
                  ∀ i, IsNoetherianAffine (X_ i) :=
  sorry

end AlgebraicGeometry
