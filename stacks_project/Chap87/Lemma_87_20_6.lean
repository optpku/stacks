module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.TypeLocality
import StacksCheckRecall

/-!
# Lemma 87.20.6

On a formal algebraic space, countable indexing, countable indexing together
with classicality, weak adicity, adic*, and Noetherianity are étale-local.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

universe u v

namespace AlgebraicGeometry

/- Lemma 87.20.6 (1): countably indexed. -/
@[stacks 0AKX] #check (AlgebraicGeometry.IsCountablyIndexedAffine.iff_etale_affine_atlas :
    ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X],
    (∀ {Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : Y ⟶ X),
        IsAffineFormalAlgebraicSpace Y → ChosenBigFppfSite.etale f → IsCountablyIndexedAffine Y) ↔
      ∃ (ι : Type (max u v))
        (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
        (π : ∀ i, X_ i ⟶ X) (c : Cofan X_) (hc : IsColimit c),
          (∀ i, IsAffineFormalAlgebraicSpace (X_ i)) ∧
            (∀ i, ChosenBigFppfSite.etale (π i)) ∧
              Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π) ∧
                ∀ i, IsCountablyIndexedAffine (X_ i))

/- Lemma 87.20.6 (2): countably indexed and classical. -/
@[stacks 0AKX] #check (AlgebraicGeometry.IsClassicalAffine.iff_etale_affine_atlas :
    ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X],
    (∀ {Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : Y ⟶ X),
        IsAffineFormalAlgebraicSpace Y → ChosenBigFppfSite.etale f →
          IsCountablyIndexedAffine Y ∧ IsClassicalAffine Y) ↔
      ∃ (ι : Type (max u v))
        (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
        (π : ∀ i, X_ i ⟶ X) (c : Cofan X_) (hc : IsColimit c),
          (∀ i, IsAffineFormalAlgebraicSpace (X_ i)) ∧
            (∀ i, ChosenBigFppfSite.etale (π i)) ∧
              Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π) ∧
                ∀ i, IsCountablyIndexedAffine (X_ i) ∧ IsClassicalAffine (X_ i))

/- Lemma 87.20.6 (3): weakly adic. -/
@[stacks 0AKX] #check (AlgebraicGeometry.IsWeaklyAdicAffine.iff_etale_affine_atlas :
    ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X],
    (∀ {Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : Y ⟶ X),
        IsAffineFormalAlgebraicSpace Y → ChosenBigFppfSite.etale f → IsWeaklyAdicAffine Y) ↔
      ∃ (ι : Type (max u v))
        (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
        (π : ∀ i, X_ i ⟶ X) (c : Cofan X_) (hc : IsColimit c),
          (∀ i, IsAffineFormalAlgebraicSpace (X_ i)) ∧
            (∀ i, ChosenBigFppfSite.etale (π i)) ∧
              Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π) ∧
                ∀ i, IsWeaklyAdicAffine (X_ i))

/- Lemma 87.20.6 (4): adic*. -/
@[stacks 0AKX] #check (AlgebraicGeometry.IsLocallyAdicStar.iff_atlas :
    ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))),
    IsLocallyAdicStar X ↔
      IsFormalAlgebraicSpace X ∧
        ∃ (ι : Type (max u v))
          (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
          (π : ∀ i, X_ i ⟶ X) (c : Cofan X_) (hc : IsColimit c),
            (∀ i, IsAffineFormalAlgebraicSpace (X_ i)) ∧
              (∀ i, etale (π i)) ∧
                Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π) ∧
                  ∀ i, IsAdicStar (X_ i))

/- Lemma 87.20.6 (5): Noetherian. -/
@[stacks 0AKX] #check (AlgebraicGeometry.IsNoetherianAffine.iff_etale_affine_atlas :
    ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X],
    (∀ {Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : Y ⟶ X),
        IsAffineFormalAlgebraicSpace Y → ChosenBigFppfSite.etale f → IsNoetherianAffine Y) ↔
      ∃ (ι : Type (max u v))
        (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
        (π : ∀ i, X_ i ⟶ X) (c : Cofan X_) (hc : IsColimit c),
          (∀ i, IsAffineFormalAlgebraicSpace (X_ i)) ∧
            (∀ i, ChosenBigFppfSite.etale (π i)) ∧
              Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π) ∧
                ∀ i, IsNoetherianAffine (X_ i))

end AlgebraicGeometry
