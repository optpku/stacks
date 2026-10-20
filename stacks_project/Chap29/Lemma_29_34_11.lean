/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.AtPoint
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import StacksCheckRecall

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 29.34.11: given an affine open neighborhood `V` of `f x`, the morphism
`f` is smooth at `x` if and only if some affine open neighborhood `U` of `x`
restricts to a standard smooth morphism over `V`. -/
@[stacks 01V7] #check
  (AlgebraicGeometry.Scheme.Hom.smoothAt_iff_exists_standardSmooth_affineChart_over :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      (x : X) (V : S.affineOpens) (hxV : f x ∈ (V : S.Opens)),
      f.SmoothAt x ↔
        ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
          ∃ e : U ≤ f ⁻¹ᵁ V,
            AlgebraicGeometry.StandardSmooth (f.resLE V U e))
