/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.Etale

/-!
# Affine étale covering families

Affine étale coverings of functors of points are detected by local
surjectivity of the coproduct of their chart maps in the fppf topology.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- An affine étale covering family has affine formal algebraic sources,
representable étale chart maps, and an fppf-locally surjective coproduct map. -/
structure IsEtaleAffineCover {S : Scheme.{u}} {ι : Type u}
    {X_ : ι → ((Over S)ᵒᵖ ⥤ Type u)} {X : (Over S)ᵒᵖ ⥤ Type u}
    (π : ∀ i, X_ i ⟶ X) : Prop where
  /-- Each chart is an affine formal algebraic space. -/
  isAffine (i : ι) : IsAffine (X_ i)
  /-- Each chart is a formal algebraic space. -/
  isFormal (i : ι) : IsFormalAlgebraicSpace (X_ i)
  /-- Each chart map is étale, hence representable by algebraic spaces. -/
  isEtale (i : ι) : Etale (π i)
  /-- The coproduct of the chart maps is fppf-locally surjective. -/
  isCover : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π)

namespace IsEtaleAffineCover

/-- Affine formal algebraic charts with étale maps and an fppf-locally
surjective coproduct form an affine étale covering family. -/
def of {S : Scheme.{u}} {ι : Type u} {X_ : ι → ((Over S)ᵒᵖ ⥤ Type u)}
    {X : (Over S)ᵒᵖ ⥤ Type u} {π : ∀ i, X_ i ⟶ X}
    (hAffine : ∀ i, IsAffine (X_ i))
    (hFormal : ∀ i, IsFormalAlgebraicSpace (X_ i))
    (hEtale : ∀ i, Etale (π i))
    (hCover : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π)) :
    IsEtaleAffineCover π where
  isAffine := hAffine
  isFormal := hFormal
  isEtale := hEtale
  isCover := hCover

/-- A family is an affine étale covering if and only if its sources are affine
formal algebraic spaces, its maps are étale, and its coproduct is
fppf-locally surjective. -/
theorem iff {S : Scheme.{u}} {ι : Type u} {X_ : ι → ((Over S)ᵒᵖ ⥤ Type u)}
    {X : (Over S)ᵒᵖ ⥤ Type u} (π : ∀ i, X_ i ⟶ X) :
    IsEtaleAffineCover π ↔
      (∀ i, IsAffine (X_ i)) ∧ (∀ i, IsFormalAlgebraicSpace (X_ i)) ∧
        (∀ i, Etale (π i)) ∧
          Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π) :=
  by
    constructor
    · intro h
      exact ⟨h.isAffine, h.isFormal, h.isEtale, h.isCover⟩
    · rintro ⟨hAffine, hFormal, hEtale, hCover⟩
      exact of hAffine hFormal hEtale hCover

/-- An affine étale covering has affine formal sources, étale chart maps,
and an fppf-locally surjective coproduct. -/
theorem spec {S : Scheme.{u}} {ι : Type u} {X_ : ι → ((Over S)ᵒᵖ ⥤ Type u)}
    {X : (Over S)ᵒᵖ ⥤ Type u} {π : ∀ i, X_ i ⟶ X} (h : IsEtaleAffineCover π) :
    (∀ i, IsAffine (X_ i)) ∧ (∀ i, IsFormalAlgebraicSpace (X_ i)) ∧
      (∀ i, Etale (π i)) ∧
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π) :=
  ⟨h.isAffine, h.isFormal, h.isEtale, h.isCover⟩

end IsEtaleAffineCover

end AlgebraicGeometry.FormalAlgebraicSpace
