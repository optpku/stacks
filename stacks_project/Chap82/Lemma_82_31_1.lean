/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import stacks_project.Chap82.Lemma_82_31_1_Splitting

/-!
# Splitting principle for Chow groups of algebraic spaces

In the good setup of Situation 82.2.1, a finite family of finite locally free
modules admits a projective flat morphism of fixed relative dimension whose Chow
pullback is injective after every good base change and on which each pulled-back
module has an invertible-quotient filtration of its rank.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 82.31.1: In Situation 82.2.1 let `X / B` be good. Let `E i` be a finite
collection of locally free `𝒪_X`-modules of rank `r i`. There exists a projective
flat morphism `π : P ⟶ X` of relative dimension `d` such that for any morphism
`g : Y ⟶ X` of good algebraic spaces over `B` the map
`π_Y^* : CH_*(Y) → CH_{* + d}(Y ×_X P)` is injective, and each `π^* (E i)` has a
filtration whose successive quotients are invertible `𝒪_P`-modules. -/
@[stacks 0ESC]
theorem exists_projective_flat_splitting {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    {ι : Type v} [Finite ι] (E : ι → X.Modules) (r : ι → ℕ)
    [∀ i, SheafOfModules.IsFiniteLocallyFreeOfRank (r i) (E i)] :
    ∃ (P : AlgebraicSpace S) (π : P ⟶ X) (d : ℕ)
      (h_projective : Projective π) (h_flat : Flat π)
      (h_dimension : RelativeDimension π d)
      (h_qs : QuasiSeparated (π ≫ pX))
      (h_lft : LocallyOfFiniteType (π ≫ pX)),
      @Hom.UniversallyInjectivePullback S B X P inferInstance inferInstance pX
          inferInstance inferInstance δ inferInstance π d h_flat h_dimension h_qs
          h_lft ∧
        ∀ i, Modules.HasInvertibleQuotientFiltrationOfLength (r i)
          ((Modules.pullback π).obj (E i)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
