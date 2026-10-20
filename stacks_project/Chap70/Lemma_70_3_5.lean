/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.Preservation.BaseChange
import StacksCheckRecall

/-!
# Base change of limit-preserving transformations

A limit-preserving transformation of functors on schemes over a base remains
limit preserving after arbitrary base change along a fibre-product square.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry Limits

universe u v

/- Lemma 70.3.5: Let `S` be a scheme and let `F`, `G`, `H : (Over S)ᵒᵖ ⥤ Type v`.
Let `a : F ⟶ G` and `b : H ⟶ G` be transformations of functors. If `a` is limit
preserving, then in a fibre-product square `P -b'→ F -a→ G` over `P -a'→ H -b→ G`
the base change `a' : P ⟶ H` is limit preserving. This `a'` is the left vertical
of the displayed square, equivalently `pullback.snd a b` when the chosen
pullback is used. -/
@[stacks 049M] #check
  (AlgebraicGeometry.Scheme.Over.IsLimitPreserving.of_isPullback :
    ∀ {S : Scheme.{u}} {F G H P : (Over S)ᵒᵖ ⥤ Type v}
      {a : F ⟶ G} {b : H ⟶ G} {a' : P ⟶ H} {b' : P ⟶ F},
      IsPullback b' a' a b →
      AlgebraicGeometry.Scheme.Over.IsLimitPreserving a →
      AlgebraicGeometry.Scheme.Over.IsLimitPreserving a')
