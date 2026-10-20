/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry.BigProetaleSite

/-- Every ambient pro-étale cover of a represented scheme admits a refinement
by a covering family in the bounded big pro-étale site, with an explicit
reindexing and factorization maps commuting with the arrows to the target. -/
theorem exists_coveringFamily_refining (X : BigProetaleSite.{u}) {T : X.carrier}
    (𝒰 : Scheme.Cover.{w} Scheme.proetalePrecoverage (X.toScheme.obj T)) :
    ∃ (J : Type u) (U : J → X.carrier) (f : ∀ j, U j ⟶ T),
      Presieve.ofArrows U f ∈ X.pretopology T ∧
        ∃ (a : J → 𝒰.I₀) (g : ∀ j, X.toScheme.obj (U j) ⟶ 𝒰.X (a j)),
          ∀ j, g j ≫ 𝒰.f (a j) = X.toScheme.map (f j) :=
  sorry

end AlgebraicGeometry.BigProetaleSite
