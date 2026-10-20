/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fpqc.Refinement
import StacksCheckRecall

/-!
# Scheme refinements of fpqc coverings of algebraic spaces

An fpqc covering family of an algebraic space admits an fpqc refinement whose
sources are schemes over the base.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

/- Lemma 73.9.5: let `S` be a scheme and let `X` be an algebraic space over
`S`. If `𝒰 = {f_i : X_i ⟶ X}` is an fpqc covering of `X`, then there exists a
refinement `𝒱 = {g_j : ofOver (T j) ⟶ X}` of `𝒰` which is an fpqc covering
and such that each `T j` is a scheme over `S`. -/
@[stacks 0419] #check
  (AlgebraicGeometry.AlgebraicSpace.FpqcCovering.exists_schemeRefinement :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}
      (family : ι → Over X) (hfamily : FpqcCovering family),
      ∃ (J : Type v) (T : J → Over S) (g : ∀ j, ofOver (T j) ⟶ X),
        FpqcCovering (fun j ↦ Over.mk (g j)) ∧
          Refines (ofArrows (fun j ↦ ofOver (T j)) g)
            (ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom)))
