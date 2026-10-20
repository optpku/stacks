/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.DirectedAffine.Reduced
import StacksCheckRecall

/-!
# Reducedness of directed affine inverse limits

The inverse limit of a directed system of reduced algebraic spaces with affine
transition morphisms is reduced.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

/- Lemma 70.4.4: Let `S` be a scheme. Let `I` be a directed set. Let
`(X_i, f_{i'i})` be an inverse system over `I` of algebraic spaces over `S`
with affine transition morphisms, and write `X = lim_i X_i` for the inverse
limit. If `X_i` is reduced for all `i`, then `X` is reduced. -/
@[stacks 0CUI] #check
  (AlgebraicGeometry.AlgebraicSpace.DirectedAffine.isReduced_limit :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} {D : OrderDual I ⥤ AlgebraicSpace S}
      [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
      [∀ i : OrderDual I, IsReduced (D.obj i)], IsReduced (Limits.limit D))
