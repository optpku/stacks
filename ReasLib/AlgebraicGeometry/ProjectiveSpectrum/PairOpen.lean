/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.FiniteSet

@[expose] public section

universe u v

namespace AlgebraicGeometry.Proj

/-- Any two points of a projective spectrum lie in a common standard open defined by a homogeneous element of positive degree. -/
theorem exists_basicOpen_pair {A : Type u} {σ : Type v} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (x1 x2 : Proj 𝒜) :
    ∃ (d : ℕ) (F : A), 0 < d ∧ F ∈ 𝒜 d ∧ x1 ∈ basicOpen 𝒜 F ∧ x2 ∈ basicOpen 𝒜 F := sorry

end AlgebraicGeometry.Proj
