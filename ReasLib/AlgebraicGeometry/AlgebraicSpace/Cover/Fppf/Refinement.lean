/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fppf

/-!
# Scheme refinements of fppf coverings of algebraic spaces

Every fppf covering family of an algebraic space over a scheme admits an fppf
refinement whose sources are schemes over the base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- An fppf covering family of an algebraic space admits an fppf refinement
whose sources are schemes over the base. -/
theorem FppfCovering.exists_schemeRefinement {S : Scheme.{u}}
    {X : AlgebraicSpace S} {ι : Type v} (X_i : ι → AlgebraicSpace S)
    (f : ∀ i, X_i i ⟶ X) (hf : FppfCovering X_i f) :
    ∃ (T : ι → Over S) (h : ∀ i, ofOver (T i) ⟶ X_i i),
      FppfCovering (fun i ↦ ofOver (T i)) (fun i ↦ h i ≫ f i) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
