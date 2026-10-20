/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.IsOpenImmersion

/-- Two separated finite-type schemes over a quasi-compact quasi-separated base which
contain the same open subscheme admit admissible blowups that embed as open subschemes
of a common separated finite-type scheme over the base. -/
theorem exists_commonExtension_after_admissibleBlowups
    {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (U X₁ X₂ : Over S) (j₁ : U ⟶ X₁) (j₂ : U ⟶ X₂)
    [IsOpenImmersion j₁.left] [IsOpenImmersion j₂.left]
    [Scheme.Hom.FiniteType U.hom] [IsSeparated U.hom]
    [Scheme.Hom.FiniteType X₁.hom] [IsSeparated X₁.hom]
    [Scheme.Hom.FiniteType X₂.hom] [IsSeparated X₂.hom] :
    ∃ (X₁' X₂' X : Over S)
      (b₁ : X₁' ⟶ X₁) (b₂ : X₂' ⟶ X₂)
      (u₁ : U ⟶ X₁') (u₂ : U ⟶ X₂')
      (i₁ : X₁' ⟶ X) (i₂ : X₂' ⟶ X) (j : U ⟶ X),
      IsAdmissibleBlowup (j₁.left).opensRange b₁.left ∧
        IsAdmissibleBlowup (j₂.left).opensRange b₂.left ∧
        IsOpenImmersion i₁.left ∧ IsOpenImmersion i₂.left ∧
        IsSeparated X.hom ∧ Scheme.Hom.FiniteType X.hom ∧
        u₁ ≫ b₁ = j₁ ∧ u₂ ≫ b₂ = j₂ ∧
        u₁ ≫ i₁ = j ∧ u₂ ≫ i₂ = j := sorry

end AlgebraicGeometry.IsOpenImmersion
