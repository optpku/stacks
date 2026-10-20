/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Basic

/-!
# Split finite locally free morphisms

This file records morphisms which are set-theoretically split by finitely many
closed subschemes and embeddings into finite locally free morphisms of this form.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A morphism is set-theoretically split by closed subschemes if finitely many closed
subschemes cover its source on points and each maps isomorphically to the target. -/
def IsSetTheoreticallySplitByClosedSubschemes
    {X Z : Scheme.{u}} (g : Z ⟶ X) : Prop :=
  ∃ (m : ℕ) (piece : Fin m → Z.IdealSheafData),
    (∀ j, IsIso ((piece j).subschemeι ≫ g)) ∧
      ∀ z : Z, ∃ j : Fin m, z ∈ ((piece j).support : Set Z)

/-- Set-theoretic splitting by closed subschemes is equivalent to the existence of a finite
point-covering family of closed subschemes whose structural composites are isomorphisms. -/
theorem isSetTheoreticallySplitByClosedSubschemes_iff
    {X Z : Scheme.{u}} (g : Z ⟶ X) :
    g.IsSetTheoreticallySplitByClosedSubschemes ↔
      ∃ (m : ℕ) (piece : Fin m → Z.IdealSheafData),
        (∀ j, IsIso ((piece j).subschemeι ≫ g)) ∧
          ∀ z : Z, ∃ j : Fin m, z ∈ ((piece j).support : Set Z) := sorry

/-- A morphism has a split finite locally free embedding if it is a closed subscheme, over its
target, of a finite locally free morphism set-theoretically split by closed subschemes. -/
def HasSplitFiniteLocallyFreeEmbedding
    {X Y : Scheme.{u}} (f : Y ⟶ X) : Prop :=
  ∃ (Z : Scheme.{u}) (i : Y ⟶ Z) (g : Z ⟶ X),
    IsClosedImmersion i ∧
      i ≫ g = f ∧
      IsFiniteLocallyFree g ∧
      g.IsSetTheoreticallySplitByClosedSubschemes

/-- Having a split finite locally free embedding is equivalent to admitting a closed immersion
over the target into a finite locally free, set-theoretically split morphism. -/
theorem hasSplitFiniteLocallyFreeEmbedding_iff
    {X Y : Scheme.{u}} (f : Y ⟶ X) :
    f.HasSplitFiniteLocallyFreeEmbedding ↔
      ∃ (Z : Scheme.{u}) (i : Y ⟶ Z) (g : Z ⟶ X),
        IsClosedImmersion i ∧
          i ≫ g = f ∧
          IsFiniteLocallyFree g ∧
          g.IsSetTheoreticallySplitByClosedSubschemes := sorry

/-- A finite morphism to an affine scheme admits a surjective finite locally free base change
whose pullback embeds into a split finite locally free morphism. -/
theorem existsFiniteLocallyFreeCover_hasSplitFiniteLocallyFreeEmbedding
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsAffine X] (hf : IsFinite f) :
    ∃ (X' : Scheme.{u}) (π : X' ⟶ X),
      Surjective π ∧
        IsFiniteLocallyFree π ∧
        Surjective (pullback.fst f π) ∧
        IsFiniteLocallyFree (pullback.fst f π) ∧
        (pullback.snd f π).HasSplitFiniteLocallyFreeEmbedding := sorry

end AlgebraicGeometry.Scheme.Hom
