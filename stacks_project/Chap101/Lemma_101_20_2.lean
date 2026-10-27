/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Points
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.GroupoidAlgebraicSpace

/- Lemma 101.20.2 (1): let `(U, R, s, t, c)` be a groupoid in algebraic spaces
such that `s, t : R ⟶ U` are flat and locally of finite presentation. Consider
the algebraic stack `X = [U / R]`. Then the image of `|R| → |U| × |U|` is an
equivalence relation. -/
@[stacks 0DTZ] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.pointsRel_equivalence :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
      [Flat G] [LocallyOfFinitePresentation G] [AlgebraicStack (SmallQuotient.quotientStack G)],
      Equivalence G.pointsRel)

/- Lemma 101.20.2 (2): let `(U, R, s, t, c)` be a groupoid in algebraic spaces
such that `s, t : R ⟶ U` are flat and locally of finite presentation. Consider
the algebraic stack `X = [U / R]`. Then `|X|` is the quotient of `|U|` by this
equivalence relation. -/
@[stacks 0DTZ] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.isPointsQuotient :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
      [Flat G] [LocallyOfFinitePresentation G] [AlgebraicStack (SmallQuotient.quotientStack G)],
      Function.Surjective G.pointsMap ∧
        ∀ u v, G.pointsRel u v ↔ G.pointsMap u = G.pointsMap v)
