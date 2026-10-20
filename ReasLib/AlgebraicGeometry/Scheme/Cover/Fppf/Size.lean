/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Size
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Limits

@[expose] public section

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Cardinal AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- Every fppf covering family admits a refining fppf covering family whose coproduct scheme has
size at most that of the target scheme. -/
theorem exists_fppfCovering_refinement_size_le {X : Scheme.{u}} {ι : Type v}
    (Xi : ι → Scheme.{u}) (f : (i : ι) → Xi i ⟶ X)
    (hf : Presieve.ofArrows Xi f ∈ fppfPrecoverage X) :
    ∃ (J : Type u) (W : J → Scheme.{u}) (g : (j : J) → W j ⟶ X)
      (hg : Presieve.ofArrows W g ∈ fppfPrecoverage X) (s : J → ι)
      (h : (j : J) → W j ⟶ Xi (s j)),
      (∀ j, h j ≫ f (s j) = g j) ∧ (∐ W).size ≤ X.size := sorry

/-- Every bundled fppf covering admits a refining bundled fppf covering whose coproduct scheme has
size at most that of the target scheme. -/
theorem exists_fppfCover_refinement_size_le {X : Scheme.{u}}
    (𝒰 : X.Cover.{v} fppfPrecoverage) :
    ∃ (𝒱 : X.Cover.{u} fppfPrecoverage)
      (φ : Precoverage.ZeroHypercover.Hom fppfPrecoverage 𝒱 𝒰),
      (∐ 𝒱.X).size ≤ X.size := sorry

end AlgebraicGeometry.Scheme
