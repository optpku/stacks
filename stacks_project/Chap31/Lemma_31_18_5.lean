/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Relative.FlatAt
import StacksCheckRecall

/-!
# Lemma 31.18.5

Pointwise flatness along a relative effective Cartier divisor.

@stack 062U
-/

@[expose] public section

/- Lemma 31.18.5: a morphism is flat at a point of a relative effective Cartier divisor when
the source local ring is Noetherian. -/
@[stacks 062U] #check
  (AlgebraicGeometry.IsRelativeEffectiveCartierDivisor.flatAt_of_mem_support :
    ∀ {X S : AlgebraicGeometry.Scheme} (f : X ⟶ S) (D : X.IdealSheafData) (x : X)
      [AlgebraicGeometry.IsRelativeEffectiveCartierDivisor f D]
      [IsNoetherianRing (X.presheaf.stalk x)],
      x ∈ D.support → AlgebraicGeometry.Scheme.Hom.flatAt f x)
