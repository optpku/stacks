/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Pullback
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace

/- Lemma 66.4.3: let `S` be a scheme. If
`P ⟶ X`, `P ⟶ Y`, `X ⟶ Z`, `Y ⟶ Z` is a cartesian square of algebraic spaces over `S`
(Stacks diagram `Z ×_Y X → X` over `Z → Y`, written in mathlib `IsPullback` order), then the
comparison of points `|P| → |X| ×_{|Z|} |Y|` is surjective. -/
@[stacks 03H4] #check
  (AlgebraicGeometry.AlgebraicSpace.Points.pullbackComparison_surjective :
    ∀ {S : Scheme.{u}} {P X Y Z : AlgebraicSpace S}
      {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
      (h : IsPullback fst snd f g),
      Function.Surjective (Points.pullbackComparison h : Points P → Points.pullbackObj f g))
