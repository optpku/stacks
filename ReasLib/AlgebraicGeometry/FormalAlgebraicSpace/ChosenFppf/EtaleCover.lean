/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Basic

/-!
# Affine étale covering families

An affine étale covering family has affine formal algebraic chart sources,
étale chart maps, and a locally surjective coproduct map.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.ChosenBigFppfSite

universe u v

namespace AlgebraicGeometry.ChosenBigFppfSite

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
variable [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]

/-- An affine étale covering family consists of affine formal algebraic
spaces with étale chart maps whose coproduct map is locally surjective. -/
structure IsEtaleAffineCover {ι : Type (max u v)}
    {X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v))}
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (π : ∀ i, X_ i ⟶ X) : Prop where
  /-- Each chart is an affine formal algebraic space. -/
  isAffine : ∀ i, IsAffineFormalAlgebraicSpace (X_ i)
  /-- Each chart map is representable by algebraic spaces and étale. -/
  isEtale : ∀ i, etale (π i)
  /-- The coproduct of the chart maps is locally surjective. -/
  isCover : ∃ (c : Cofan X_) (hc : IsColimit c),
    Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π)

namespace IsEtaleAffineCover

/-- Affine charts with étale maps and a locally surjective coproduct map
form an affine étale covering family. -/
def of {ι : Type (max u v)} {X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v))}
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))} {π : ∀ i, X_ i ⟶ X}
    (hAffine : ∀ i, IsAffineFormalAlgebraicSpace (X_ i))
    (hEtale : ∀ i, etale (π i))
    (hCover : ∃ (c : Cofan X_) (hc : IsColimit c),
      Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π)) :
    IsEtaleAffineCover π where
  isAffine := hAffine
  isEtale := hEtale
  isCover := hCover

/-- A family is an affine étale covering family if and only if its sources
are affine formal algebraic spaces, its maps are étale, and its coproduct map
is locally surjective. -/
theorem iff {ι : Type (max u v)}
    {X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v))}
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))} (π : ∀ i, X_ i ⟶ X) :
    IsEtaleAffineCover π ↔
      (∀ i, IsAffineFormalAlgebraicSpace (X_ i)) ∧
        (∀ i, etale (π i)) ∧
          ∃ (c : Cofan X_) (hc : IsColimit c),
            Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π) :=
  by
    constructor
    · intro h
      exact ⟨h.isAffine, h.isEtale, h.isCover⟩
    · rintro ⟨hAffine, hEtale, hCover⟩
      exact of hAffine hEtale hCover

/-- An affine étale covering family has affine sources, étale and
representable chart maps, and a locally surjective coproduct map. -/
theorem spec {ι : Type (max u v)}
    {X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v))}
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))} {π : ∀ i, X_ i ⟶ X}
    (h : IsEtaleAffineCover π) :
    (∀ i, IsAffineFormalAlgebraicSpace (X_ i)) ∧
      (∀ i, etale (π i)) ∧ (∀ i, representableByAlgebraicSpaces (π i)) ∧
        ∃ (c : Cofan X_) (hc : IsColimit c),
          Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π) :=
  by
    exact ⟨h.isAffine, h.isEtale, fun i => (h.isEtale i).1, h.isCover⟩

end IsEtaleAffineCover

end AlgebraicGeometry.ChosenBigFppfSite
