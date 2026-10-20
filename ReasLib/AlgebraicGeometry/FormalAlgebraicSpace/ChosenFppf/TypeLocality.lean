/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.TypeConditions

/-!
# Étale locality of affine formal algebraic space types

Countable indexing, countable indexing together with classicality, weak
adicity, and Noetherianity hold on every affine étale chart of a formal
algebraic space if and only if they hold on every chart of some affine
étale atlas.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry

/-- Every affine étale chart of a formal algebraic space is countably indexed
if and only if it admits an affine étale atlas with countably indexed charts. -/
theorem IsCountablyIndexedAffine.iff_etale_affine_atlas
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    (∀ {Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : Y ⟶ X),
        IsAffineFormalAlgebraicSpace Y →
          ChosenBigFppfSite.etale f → IsCountablyIndexedAffine Y) ↔
      ∃ (ι : Type (max u v))
        (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
        (π : ∀ i, X_ i ⟶ X) (c : Cofan X_) (hc : IsColimit c),
          (∀ i, IsAffineFormalAlgebraicSpace (X_ i)) ∧
            (∀ i, ChosenBigFppfSite.etale (π i)) ∧
              Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π) ∧
                ∀ i, IsCountablyIndexedAffine (X_ i) :=
  sorry

/-- Every affine étale chart of a formal algebraic space is countably indexed
and classical if and only if it admits an affine étale atlas whose charts
are countably indexed and classical. -/
theorem IsClassicalAffine.iff_etale_affine_atlas
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    (∀ {Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : Y ⟶ X),
        IsAffineFormalAlgebraicSpace Y → ChosenBigFppfSite.etale f →
          IsCountablyIndexedAffine Y ∧ IsClassicalAffine Y) ↔
      ∃ (ι : Type (max u v))
        (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
        (π : ∀ i, X_ i ⟶ X) (c : Cofan X_) (hc : IsColimit c),
          (∀ i, IsAffineFormalAlgebraicSpace (X_ i)) ∧
            (∀ i, ChosenBigFppfSite.etale (π i)) ∧
              Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π) ∧
                ∀ i, IsCountablyIndexedAffine (X_ i) ∧ IsClassicalAffine (X_ i) :=
  sorry

/-- Every affine étale chart of a formal algebraic space is weakly adic if
and only if it admits an affine étale atlas with weakly adic charts. -/
theorem IsWeaklyAdicAffine.iff_etale_affine_atlas
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    (∀ {Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : Y ⟶ X),
        IsAffineFormalAlgebraicSpace Y →
          ChosenBigFppfSite.etale f → IsWeaklyAdicAffine Y) ↔
      ∃ (ι : Type (max u v))
        (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
        (π : ∀ i, X_ i ⟶ X) (c : Cofan X_) (hc : IsColimit c),
          (∀ i, IsAffineFormalAlgebraicSpace (X_ i)) ∧
            (∀ i, ChosenBigFppfSite.etale (π i)) ∧
              Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π) ∧
                ∀ i, IsWeaklyAdicAffine (X_ i) :=
  sorry

/-- Every affine étale chart of a formal algebraic space is Noetherian if
and only if it admits an affine étale atlas with Noetherian charts. -/
theorem IsNoetherianAffine.iff_etale_affine_atlas
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    (∀ {Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : Y ⟶ X),
        IsAffineFormalAlgebraicSpace Y →
          ChosenBigFppfSite.etale f → IsNoetherianAffine Y) ↔
      ∃ (ι : Type (max u v))
        (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
        (π : ∀ i, X_ i ⟶ X) (c : Cofan X_) (hc : IsColimit c),
          (∀ i, IsAffineFormalAlgebraicSpace (X_ i)) ∧
            (∀ i, ChosenBigFppfSite.etale (π i)) ∧
              Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π) ∧
                ∀ i, IsNoetherianAffine (X_ i) :=
  sorry

end AlgebraicGeometry
