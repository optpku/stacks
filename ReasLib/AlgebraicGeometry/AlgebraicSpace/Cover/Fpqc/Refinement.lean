/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fpqc

/-!
# Scheme refinements of fpqc coverings of algebraic spaces

Every fpqc covering family of an algebraic space over a scheme admits an fpqc
refinement whose sources are schemes over the base.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- An fpqc covering family of an algebraic space admits an fpqc refinement
whose sources are schemes over the same base. -/
theorem FpqcCovering.exists_schemeRefinement {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} (family : ι → Over X) (hfamily : FpqcCovering family) :
    ∃ (J : Type v) (T : J → Over S) (g : ∀ j, ofOver (T j) ⟶ X),
      FpqcCovering (fun j ↦ Over.mk (g j)) ∧
        Refines (ofArrows (fun j ↦ ofOver (T j)) g)
          (ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
