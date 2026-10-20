/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Proetale.Family

/-!
# Finite affine refinements of pro-étale covers

Pro-étale covers of affine schemes have finite refinements by affine open
subschemes of their members.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme.Proetale

/-- A pro-étale cover of an affine scheme has a finite affine weakly étale
refinement whose component maps into the original cover are open immersions. -/
theorem exists_finite_affineRefinement {T : Scheme.{u}} [IsAffine T]
    (𝒰 : T.Cover Scheme.proetalePrecoverage) :
    ∃ (𝒱 : T.AffineCover (@WeaklyEtale)) (f : 𝒱.cover ⟶ 𝒰.forgetQc),
      Finite 𝒱.I₀ ∧ ∀ j, IsOpenImmersion (f.h₀ j) := sorry

/-- A pro-étale covering family of an affine scheme has a finite affine weakly
étale refinement, with open immersions into selected members of the original
family. -/
theorem exists_finite_affineRefinement_family {T : Scheme.{u}} [IsAffine T]
    {ι : Type v} {family : ι → Over T} (h : IsCovering family) :
    ∃ (𝒱 : T.AffineCover (@WeaklyEtale)) (s : 𝒱.I₀ → ι)
      (f : (j : 𝒱.I₀) → Spec (𝒱.X j) ⟶ (family (s j)).left),
      Finite 𝒱.I₀ ∧ (∀ j, f j ≫ (family (s j)).hom = 𝒱.f j) ∧
        ∀ j, IsOpenImmersion (f j) := sorry

end AlgebraicGeometry.Scheme.Proetale
