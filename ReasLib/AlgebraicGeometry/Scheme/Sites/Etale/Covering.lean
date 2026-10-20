/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- An indexed family belongs to the étale precoverage exactly when its images
jointly cover the target and every morphism in the family is étale. -/
theorem ofArrows_mem_etalePrecoverage_iff {T : Scheme.{u}} {ι : Type v}
    {X : ι → Scheme.{u}} (f : ∀ i, X i ⟶ T) :
    Presieve.ofArrows X f ∈ etalePrecoverage T ↔
      ((∀ x : T, ∃ i, x ∈ Set.range (f i)) ∧ ∀ i, Etale (f i)) := sorry

end AlgebraicGeometry.Scheme
