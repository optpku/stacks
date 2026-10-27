/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Associated
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-! # Abelian categories of modules on associated sites -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The original-universe abelian-group sheafification reflector on an associated
`τ`-site preserves finite limits. -/
theorem associatedTopology_sheafification_preservesFiniteLimits
    (X : GroupoidsOver S) (τ : StandardTopology) :
    PreservesFiniteLimits
      ((sheafToPresheaf (X.associatedTopology τ) AddCommGrpCat.{u}).leftAdjoint) := sorry

/-- The associated `τ`-site has left exact abelian-group sheafification in the
original universe, using its canonical weak sheafification reflector. -/
instance associatedTopology_hasSheafify (X : GroupoidsOver S) (τ : StandardTopology) :
    HasSheafify (X.associatedTopology τ) AddCommGrpCat.{u} where
  isRightAdjoint := associatedTopology_hasWeakSheafify X τ
  isLeftExact := associatedTopology_sheafification_preservesFiniteLimits X τ

end AlgebraicGeometry.GroupoidsOver
