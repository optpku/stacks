/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Basic

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.IsZariskiLocalAtTarget

/-- A target-local property of scheme morphisms holds exactly when it holds after restriction
along every member of some open cover of the target. -/
theorem iff_exists_openCover
    {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme}
    [AlgebraicGeometry.IsZariskiLocalAtTarget P]
    {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) :
    P f ↔ ∃ 𝒰 : S.OpenCover.{u}, ∀ i : 𝒰.I₀, P (f ∣_ ((𝒰.f i).opensRange)) := sorry

end AlgebraicGeometry.IsZariskiLocalAtTarget
