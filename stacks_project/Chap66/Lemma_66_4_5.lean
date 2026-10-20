/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Presentation.Points
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

/- Lemma 66.4.5 (1): let `S` be a scheme. Let `X` be an algebraic space over `S`. Let
`X = U / R` be a presentation of `X`. Then the image of `|R| → |U| × |U|` is an
equivalence relation on `|U|`. -/
@[stacks 03BW] #check
  (AlgebraicGeometry.AlgebraicSpace.Presentation.pointsRel_equivalence :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (P : Presentation X),
      Equivalence P.pointsRel)

/- Lemma 66.4.5 (2): let `S` be a scheme. Let `X` be an algebraic space over `S`. Let
`X = U / R` be a presentation of `X`. Then `|X|` is the quotient of `|U|` by this
equivalence relation. -/
@[stacks 03BW] #check
  (AlgebraicGeometry.AlgebraicSpace.Presentation.isPointsQuotient :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (P : Presentation X),
      Function.Surjective P.pointsMap ∧
        ∀ u v, P.pointsRel u v ↔ P.pointsMap u = P.pointsMap v)
