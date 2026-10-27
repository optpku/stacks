/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import ReasLib.CategoryTheory.Filtration.Invertible
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Projective.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.FlatPullback.UniversallyInjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute.Relative

/-! # The splitting principle for Chow groups of algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- A finite family of finite locally free modules on a good algebraic space over an
absolutely quasi-separated universally catenary base admits a projective flat splitting
morphism of fixed relative dimension. Its canonical Chow pullback is injective after every
good base change in every degree, and each pulled-back module has a filtration of its rank
with tensor-invertible successive quotients. -/
theorem exists_projective_flat_splitting {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    {ι : Type v} [Finite ι] (E : ι → X.Modules) (r : ι → ℕ)
    [∀ i, SheafOfModules.IsFiniteLocallyFreeOfRank (r i) (E i)] :
    ∃ (P : AlgebraicSpace S) (π : P ⟶ X) (d : ℕ),
      Projective π ∧ Flat π ∧ RelativeDimension π d ∧
        QuasiSeparated (π ≫ pX) ∧ LocallyOfFiniteType (π ≫ pX) ∧
        Hom.UniversallyInjectivePullback pX δ π d ∧
        ∀ i, CategoryTheory.HasInvertibleQuotientFiltrationOfLength (r i)
          ((Modules.pullback π).obj (E i)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
